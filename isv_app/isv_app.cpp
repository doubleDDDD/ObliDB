/*
 * Copyright (C) 2011-2017 Intel Corporation. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in
 *     the documentation and/or other materials provided with the
 *     distribution.
 *   * Neither the name of Intel Corporation nor the names of its
 *     contributors may be used to endorse or promote products derived
 *     from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

// This sample is confined to the communication between a SGX client platform
// and an ISV Application Server. 



#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <unistd.h>
#include <time.h>
#include <math.h>
#include <iostream>
#include <fstream>
#include <sstream>
#include <set>
#include <unordered_set>
#include <algorithm>
// Needed for definition of remote attestation messages.
#include "remote_attestation_result.h"

#include "isv_enclave_u.h"

// Needed to call untrusted key exchange library APIs, i.e. sgx_ra_proc_msg2.
#include "sgx_ukey_exchange.h"

// Needed to get service provider's information, in your real project, you will
// need to talk to real server.
#include "network_ra.h"

// Needed to create enclave and do ecall.
#include "sgx_urts.h"

// Needed to query extended epid group id.
// #include "sgx_uae_epid.h"
#include "sgx_uae_service.h"

#include "service_provider.h"
#include "../isv_enclave/definitions.h"//structs, enums, fixed constants

#include "extraio.h"

#ifndef SAFE_FREE
#define SAFE_FREE(ptr) {if (NULL != (ptr)) {free(ptr); (ptr) = NULL;}}
#endif

// In addition to generating and sending messages, this application
// can use pre-generated messages to verify the generation of
// messages and the information flow.
#include "sample_messages.h"


//#define ENCLAVE_PATH "isv_enclave.signed.so"
#define ENCLAVE_PATH "./isv_enclave.signed.so"

//use these to keep track of all the structures and their types (added by me, not part of sample code)
// 目前的set支持10张表，NUM_STRUCTURES=10，10张表可以都在一个file里搞定
int oblivStructureSizes[NUM_STRUCTURES] = {0};
int oblivStructureTypes[NUM_STRUCTURES] = {0};
uint8_t* oblivStructures[NUM_STRUCTURES] = {0}; //hold pointers to start of each oblivious data structure
int oblivStructureQueryTypes[NUM_STRUCTURES] = {0};  // 查询类型
RW_Type oblivStructureStorageTypes[NUM_STRUCTURES] = {MEMORY};  // 存储类型

char* globaltablename;  // 用来暂存tablename的，暂时不支持多线程并发去 access db
Schema* globalschema;  // 同上

// 全局打开表的数组
oblidbextraio::DBTable* dbtables[NUM_STRUCTURES] = {nullptr};

FILE *readFile = NULL;

uint8_t* msg1_samples[] = { msg1_sample1, msg1_sample2 };
uint8_t* msg2_samples[] = { msg2_sample1, msg2_sample2 };
uint8_t* msg3_samples[MSG3_BODY_SIZE] = { msg3_sample1, msg3_sample2 };
uint8_t* attestation_msg_samples[] =
    { attestation_msg_sample1, attestation_msg_sample2};

oblidbextraio::StorageEngine* storageengine = nullptr;
unsigned char gkey[L_SGX_AESGCM_KEY_SIZE]={0};  /* 用来保存秘钥的 */

// query 对结果表的处理 + 一个回调 用户自行处置

void
ReOpenDB(oblidbextraio::HeaderPage* header_page, sgx_enclave_id_t enclave_id, int status)
{
	int i, pre_offset;

	unsigned char lkey[16];
	int recordcn = header_page->GetRecordCount();
	int cur_offset = header_page->GetOffset();
    bool validkey = header_page->ValidKey();
	header_page->GetKey(lkey);
	// std::string _key(key);

	std::cout 
		<< "record count:" << recordcn 
		<< ",current offset:" << cur_offset 
		<< ",validkey:" << validkey << std::endl;
	
	// for(int j=0;j<16;++j){
	// 	printf("last %c\n", lkey[j]);
	// }

	// update with schema
	for(i=0;i<recordcn;++i)
	{
		int offset = header_page->GetRecordOffset(i);
		assert(offset != -1);
		char *raw_name = reinterpret_cast<char *>(header_page->GetData() + offset);
		int32_t rootpage = *reinterpret_cast<int32_t *>(header_page->GetData() + offset + 32);
        std::string tbname(raw_name);
		int encBlockSize = *reinterpret_cast<int *>(header_page->GetData() + offset + 36);
		int rownum = *reinterpret_cast<int *>(header_page->GetData() + offset + 40);
		int type = *reinterpret_cast<int *>(header_page->GetData() + offset + 44);
		int numFields = *reinterpret_cast<int *>(header_page->GetData() + offset + 48);

		std::cout
			<< "index:" << i
			<< ",table name:" << tbname 
			<< ",root page id:" << rootpage 
			<< ",encblocksize:" << encBlockSize
			<< ",row num:" << rownum
			<< ",type:" << type 
			<< ",numFields:" << numFields << std::endl;

		// offset += 48;
		Schema schema;
		schema.numFields = numFields;
		for(int j=0;j<numFields;++j){
			schema.fieldOffsets[j] = \
				*reinterpret_cast<int *>(header_page->GetData() + offset + 52 + j*12 + 0);
			schema.fieldSizes[j] = \
				*reinterpret_cast<int *>(header_page->GetData() + offset + 52 + j*12 + 4);
			schema.fieldTypes[j] = \
				static_cast<DB_Type>(*reinterpret_cast<int *>(header_page->GetData() + offset + 52 + j*12 + 8));
			
			std::cout 
				<< "index:" << j
				<< ",offset:" << schema.fieldOffsets[j] 
				<< ",size:" << schema.fieldSizes[j] 
				<< ",type:" << schema.fieldTypes[j] << std::endl;
		}

		/**
		 * 恢复 table 在内存中的数据结构, 游标按照最大去 set
		 */
		assert(dbtables[i]==nullptr);
		dbtables[i] = new oblidbextraio::DBTable(
			storageengine->buffer_pool_manager_, 
			storageengine->disk_manager_, 
			tbname,
			encBlockSize, 
			rownum, 
			type, 
			rownum, rootpage);
		
		oblivStructureSizes[i] = rownum;
		oblivStructureTypes[i] = type;
		oblivStructureStorageTypes[i] = DISK;

		Obliv_Type _type = static_cast<Obliv_Type>(type);
		char* _tbname = const_cast<char *>(tbname.c_str());

		// set sgx key
		ReopenTable(
			enclave_id, 
			(int*)&status, 
			i,
			&schema,
			lkey,
			rownum, 
			_tbname, 
			tbname.length(), 
			_type);
	}

	return;
}

/**
 * init db, 打开数据库，即open, 就是连接数据库的过程，这个地方就是 single thread
 * 如果文件不存在则创建
 * header page 的插入是创建表或 open 表时候的操作
 */
void
ConnectDB(sgx_enclave_id_t enclave_id, int status)
{
    std::string db_file_name = "/home/hdd/workspace/ssd_mount/dbpath/oblidbtest.odb";

    struct stat buffer;
    bool is_file_exist = (stat(db_file_name.c_str(), &buffer) == 0);
    storageengine = new oblidbextraio::StorageEngine(db_file_name);

    if (!is_file_exist) {
        oblidbextraio::page_id_t header_page_id;

        auto header_page = 
            static_cast<oblidbextraio::HeaderPage *>(storageengine->buffer_pool_manager_->NewPage(header_page_id));  /* new的过程本身是加锁的 */
        assert(header_page_id == HEADER_PAGE_ID);
        header_page->WLatch();
        header_page->Init();

		assert(gkey);
		if(!header_page->ValidKey()){
			header_page->SetKey(gkey, L_SGX_AESGCM_KEY_SIZE);
			header_page->SetKeyValidFlag(true);
			storageengine->buffer_pool_manager_->UnpinPage(HEADER_PAGE_ID, true);
		}

        storageengine->buffer_pool_manager_->UnpinPage(header_page_id, true);  /* 虽然没有任何写操作，但是必须dirty */
        header_page->WUnlatch();
    } else {
		// re open/connect db
		auto header_page = 
            static_cast<oblidbextraio::HeaderPage *>(storageengine->buffer_pool_manager_->FetchPage(HEADER_PAGE_ID));
		if(header_page == nullptr){
			std::cerr << "re open db failure!" << std::endl;
			exit(-1);
		}

		// 要把 app 与 sgx 中的一些全局的数据结构恢复
		ReOpenDB(header_page, enclave_id, status);
	}
}

void
ocall_settablekey(
	unsigned char* obliv_key, int keylen)
{
    // assert(storageengine);
    auto header_page =
        static_cast<oblidbextraio::HeaderPage *>(storageengine->buffer_pool_manager_->FetchPage(HEADER_PAGE_ID));
    if(!header_page){ return; }

	// char keycontainer[16];
	// memcpy(keycontainer, obliv_key, keylen);
	// printf("out key is %s, validkey: %d\n", keycontainer, header_page->ValidKey());
	// printf("key is %s\n", obliv_key);  // can not access memory in sgx

	assert(gkey);
	header_page->WLatch();
	// try set sgx, 如果是 reopen 的，这里直接 pass
	if(!header_page->ValidKey()){
		header_page->SetKey(gkey, keylen);
		header_page->SetKeyValidFlag(true);
		storageengine->buffer_pool_manager_->UnpinPage(HEADER_PAGE_ID, true);
	}
    header_page->WUnlatch();

	return;
}

void
ocall_outchar(int index, unsigned char c)
{
	// printf("out char %d of key %c\n", index, c);
	gkey[index] = c;
	// printf("final %s\n", gkey);
	return;
}

void
CloseDB()
{
	for(int u=0;u<NUM_STRUCTURES;++u){
		if(!dbtables[u]) { continue; }
		delete dbtables[u];
	}

	storageengine->buffer_pool_manager_->FlushAllDirtyPage();
	delete storageengine;
}

void
CrackTable(int index, sgx_enclave_id_t enclave_id, int status)
{
	int i;
	oblidbextraio::DBTable* table = dbtables[index];
	oblidbextraio::Tuple tuple;

	for(i=0;i<table->TableSize();++i){
		if(!table->GetTuple(tuple, i)){
			std::cerr << "Get table failure" << std::endl;
			exit(-1);
		}
		decryptOneBlock(enclave_id, (int*)&status, (Encrypted_Linear_Scan_Block*)(tuple.GetData()), index);
	}

	return;
}

void
CrackTables(sgx_enclave_id_t enclave_id, int status)
{
	// oblidbextraio::DBTable* dbtables[NUM_STRUCTURES] = {nullptr};
	int i;

	for(i=0;i<NUM_STRUCTURES;++i)
	{
		if(!dbtables[i]){ continue; }
		printf("Crack Table %d\n", i);
		CrackTable(i, enclave_id, status);
	}

	return;
}

// Some utility functions to output some of the data structures passed between
// the ISV app and the remote attestation service provider.
void PRINT_BYTE_ARRAY(
    FILE *file, void *mem, uint32_t len)
{
    if(!mem || !len)
    {
        fprintf(file, "\n( null %d %d)\n", mem, len);
        return;
    }
    uint8_t *array = (uint8_t *)mem;
    fprintf(file, "%u bytes:\n{\n", len);
    uint32_t i = 0;
    for(i = 0; i < len - 1; i++)
    {
        fprintf(file, "0x%x, ", array[i]);
        if(i % 8 == 7) fprintf(file, "\n");
    }
    fprintf(file, "0x%x ", array[i]);
    fprintf(file, "\n}\n");
}


void PRINT_ATTESTATION_SERVICE_RESPONSE(
    FILE *file,
    ra_samp_response_header_t *response)
{
    if(!response)
    {
        fprintf(file, "\t\n( null )\n");
        return;
    }

    fprintf(file, "RESPONSE TYPE:   0x%x\n", response->type);
    fprintf(file, "RESPONSE STATUS: 0x%x 0x%x\n", response->status[0],
            response->status[1]);
    fprintf(file, "RESPONSE BODY SIZE: %u\n", response->size);

    if(response->type == TYPE_RA_MSG2)
    {
        sgx_ra_msg2_t* p_msg2_body = (sgx_ra_msg2_t*)(response->body);

        /*
        fprintf(file, "MSG2 gb - ");
        PRINT_BYTE_ARRAY(file, &(p_msg2_body->g_b), sizeof(p_msg2_body->g_b));

        fprintf(file, "MSG2 spid - ");
        PRINT_BYTE_ARRAY(file, &(p_msg2_body->spid), sizeof(p_msg2_body->spid));

        fprintf(file, "MSG2 quote_type : %hx\n", p_msg2_body->quote_type);

        fprintf(file, "MSG2 kdf_id : %hx\n", p_msg2_body->kdf_id);

        fprintf(file, "MSG2 sign_gb_ga - ");
        PRINT_BYTE_ARRAY(file, &(p_msg2_body->sign_gb_ga),
                         sizeof(p_msg2_body->sign_gb_ga));

        fprintf(file, "MSG2 mac - ");
        PRINT_BYTE_ARRAY(file, &(p_msg2_body->mac), sizeof(p_msg2_body->mac));

        fprintf(file, "MSG2 sig_rl - ");
        PRINT_BYTE_ARRAY(file, &(p_msg2_body->sig_rl),
                         p_msg2_body->sig_rl_size);
        */
    }
    else if(response->type == TYPE_RA_ATT_RESULT)
    {
        sample_ra_att_result_msg_t *p_att_result =
            (sample_ra_att_result_msg_t *)(response->body);
        /*
        fprintf(file, "ATTESTATION RESULT MSG platform_info_blob - ");
        PRINT_BYTE_ARRAY(file, &(p_att_result->platform_info_blob),
                         sizeof(p_att_result->platform_info_blob));

        fprintf(file, "ATTESTATION RESULT MSG mac - ");
        PRINT_BYTE_ARRAY(file, &(p_att_result->mac), sizeof(p_att_result->mac));

        fprintf(file, "ATTESTATION RESULT MSG secret.payload_tag - %u bytes\n",
                p_att_result->secret.payload_size);

        fprintf(file, "ATTESTATION RESULT MSG secret.payload - ");
        PRINT_BYTE_ARRAY(file, p_att_result->secret.payload,
                p_att_result->secret.payload_size);
        */
    }
    else
    {
        fprintf(file, "\nERROR in printing out the response. "
                       "Response of type not supported %d\n", response->type);
    }
}

/*
 * Begin Saba's Code
 * OCALLS GO HERE
 *
 * */
void ocall_showquery(int tableid, int querytype){
	oblivStructureQueryTypes[tableid] = querytype;
}

void ocall_print(const char *str)
{
    /* Proxy/Bridge will check the length and null-terminate
     * the input string to prevent buffer overflow.
     */
    printf("%s", str);
    fflush(stdout);  /* 立刻输出 */
}

void
ocall_read_block(
    int structureId, int index, int blockSize, void *buffer)
{
	//read in to buffer
	if(blockSize == 0){
		printf("unkown oblivious data type\n");
		return;
	}

	if(dbtables[structureId]){
		// read disk table
		assert(dbtables[structureId]);
		assert(storageengine);

		oblidbextraio::DBTable* table = dbtables[structureId];
		// printf("structureId is %d\n", structureId);
		// RW_Type storagetype = static_cast<RW_Type>(table->Type());
		oblidbextraio::Tuple tuple;
		if(!table->GetTuple(tuple, index)){
			std::cerr << "Read disk table failure!" << std::endl;
			exit(-1);
		}
		// std::cout << tuple.GetData() << std::endl;
		assert(blockSize==tuple.GetSize());
		memcpy(buffer, tuple.GetData(), blockSize);	
	} else {
		// read memory table
		memcpy(
			buffer, oblivStructures[structureId]+((long)index*blockSize), blockSize);
	}

	return;
	//printf("heer\n");fflush(stdout);
	//printf("index: %d, blockSize: %d structureId: %d\n", index, blockSize, structureId);
	//printf("start %d, addr: %d, expGap: %d\n", oblivStructures[structureId], oblivStructures[structureId]+index*blockSize, index*blockSize);fflush(stdout);
	//printf("beginning of mac(app)? %d\n", ((Encrypted_Linear_Scan_Block*)(oblivStructures[structureId]+(index*encBlockSize)))->macTag[0]);
	//printf("beginning of mac(buf)? %d\n", ((Encrypted_Linear_Scan_Block*)(buffer))->macTag[0]);
}

/**
 * write out from buffer
 * index is the row number
 */
void
ocall_write_block(
    int structureId, int index, int blockSize, void *buffer)
{
	if(blockSize == 0){
		printf("unkown oblivious data type\n");
		return;
	}

	// printf("ocall_write_block: %d,%d,%d\n", structureId, index, blockSize);
	RW_Type storagetype = oblivStructureStorageTypes[structureId];

    if(storagetype == MEMORY){
        memcpy(oblivStructures[structureId]+((long)index*blockSize), buffer, blockSize);
    } else {
        assert(storageengine);

		/* 根据 structureId 找到对应的 table 对象 */
		assert(dbtables[structureId]);
		oblidbextraio::DBTable* table = dbtables[structureId];

		/* 构造 tuple 对象 */
		oblidbextraio::Tuple tuple(blockSize, (char*)buffer);

		/**
		 * table->Cursor() 代表当前准备写入的下标
		 * index 代表的是 tuple index
		 */
		if (index < table->Cursor()) {
			// printf("update\n");
			/* update tuple */
			if(!table->UpdateTuple(tuple, index)){
				std::cerr << "Update failure, re run!" << std::endl;
				exit(-1);
			}
		} else {
			/* insert tuple */
			// printf("insert\n");
			if(!table->InsertTuple(tuple, index)){
				std::cerr << "Insert failure, re run!" << std::endl;
				exit(-1);
			}
			table->IncrementCursor();
		}
    }

	return;

	//printf("data: %d %d %d %d\n", structureId, index, blockSize, ((int*)buffer)[0]);fflush(stdout);
	//printf("data: %d %d %d\n", structureId, index, blockSize);fflush(stdout);

	/*if(structureId == 3 && blockSize > 1) {
		blockSize = 8000000;//temp
		printf("in structure 3");fflush(stdout);
	}*/
	//printf("here! blocksize %d, index %d, structureId %d\n", blockSize, index, structureId);
	//printf("here2\n");
	//debug code
	//printf("pointer 1 %p, pointer 2 %p, difference %d\n", oblivStructures[structureId], oblivStructures[structureId]+(index*encBlockSize), (index*encBlockSize));
	//printf("beginning of mac? %d\n", ((Encrypted_Linear_Scan_Block*)(oblivStructures[structureId]+(index*encBlockSize)))->macTag[0]);
}

void ocall_respond( uint8_t* message, size_t message_size, uint8_t* gcm_mac){
	printf("ocall response\n");
}

/**
 * 返回表的 schema 是没有给到外面的
 */
void newStructureinmemory(int newId, Obliv_Type type, int size)
{
    // printf("app: %d initializing structure type %d of capacity %d blocks\n", newId, type, size);
    int encBlockSize = getEncBlockSize(type);
    oblivStructureSizes[newId] = size;
    oblivStructureTypes[newId] = type;
    long val = (long)encBlockSize*size; /* malloc memory in 不可信内存 */
    oblivStructures[newId] = (uint8_t*)malloc(val);
    if(!oblivStructures[newId]) {
        printf("failed to allocate space (%ld bytes) for structure\n", val);
        fflush(stdout);
    }

    return;
}

/** 
 * create table 数据库表，即创建表
 */
void
newStructureinperist(int newId, Obliv_Type type, int rownum)
{
    assert(storageengine);
	// printf("Create new table:%d,row num:%d\n", newId, rownum);

	int encBlockSize = getEncBlockSize(type);
    if(type == TYPE_ORAM || type == TYPE_TREE_ORAM) {
		encBlockSize = sizeof(Encrypted_Oram_Bucket);
	}
    oblivStructureSizes[newId] = rownum;
    oblivStructureTypes[newId] = type;

	/**
	 * 数据库初始化的时候创建过 root page
	 */
    auto header_page =
        static_cast<oblidbextraio::HeaderPage *>(storageengine->buffer_pool_manager_->FetchPage(HEADER_PAGE_ID));

    if(!header_page){
        std::cerr << "new table failure, get header page failure!" << std::endl;
        CloseDB();
        exit(-1);
    }
	
	std::string tbname(globaltablename);
	dbtables[newId] = new oblidbextraio::DBTable(
		storageengine->buffer_pool_manager_,
		storageengine->disk_manager_, tbname, encBlockSize, rownum, type, 0);
	
	oblidbextraio::DBTable* p = dbtables[newId];
	oblidbextraio::TableHeap* thp = p->GetTableHeap();
	oblidbextraio::page_id_t first_page_id = thp->GetFirstPageId();
	// printf("get new root id:%d\n", first_page_id);

    header_page->WLatch();

    // insert table header
    if (!header_page->InsertRecord(
		tbname, globalschema, first_page_id, encBlockSize, rownum, (int)type))
	{
        std::cerr << "insert failure!" << std::endl;
        header_page->WUnlatch();
		// p->DeallocateOnePage(); 复杂，在 sgx 中判断重名
		delete p;
        CloseDB();
        exit(-1);
    }

    storageengine->buffer_pool_manager_->UnpinPage(HEADER_PAGE_ID, true);
    header_page->WUnlatch();

    return;
}

/**
 * 维护一个数组，表明 table 的类型
 * int oblivStructureStorageTypes[NUM_STRUCTURES] = {MEMORY};  // 存储类型
 */
void
ocall_newStructure(
	int newId, Obliv_Type type, int size, TABLE_TYPE tableType)
{	
    switch (tableType)
    {
    case RET:
    case TEMP:
		printf("Create new memory table:%d,row num:%d\n", newId, size);
        newStructureinmemory(newId, type, size);
		oblivStructureStorageTypes[newId] = MEMORY;
        break;
    default:
		printf("Create new disk table:%d,row num:%d\n", newId, size);
        newStructureinperist(newId, type, size);
		oblivStructureStorageTypes[newId] = DISK;
        break;
    }

	return;

	//this is actual size, the logical size will be smaller for orams
    // //printf("app: initializing structure type %d of capacity %d blocks\n", type, size);
    // int encBlockSize = getEncBlockSize(type);
    // if(type == TYPE_ORAM || type == TYPE_TREE_ORAM) encBlockSize = sizeof(Encrypted_Oram_Bucket);
    // //printf("Encrypted blocks of this type get %d bytes of storage\n", encBlockSize);
    // oblivStructureSizes[newId] = size;
    // oblivStructureTypes[newId] = type;
    // long val = (long)encBlockSize*size;
    // //printf("mallocing %ld bytes\n", val);
    // oblivStructures[newId] = (uint8_t*)malloc(val);
    // if(!oblivStructures[newId]) {
    // 	printf("failed to allocate space (%ld bytes) for structure\n", val);fflush(stdout);
    // }
}

void ocall_deleteStructure(int structureId) {
	oblivStructureSizes[structureId] = 0;
	oblivStructureTypes[structureId] = 0;
	free(oblivStructures[structureId]); //hold pointers to start of each oblivious data structure
}

void ocall_open_read(int tableSize){
	char tableName[20];
	sprintf(tableName, "testTable%d", tableSize);
	//printf("table's name is %s\n", tableName);fflush(stdout);
	readFile = fopen((char*)tableName, "r");
	//printf("here a function is called\n");fflush(stdout);
}

void ocall_make_name(void *name, int tableSize){
	sprintf((char*)name, "testTable%d", tableSize);
}

void ocall_write_file(const void *src, int dsize, int tableSize){
	char tableName[20];
	sprintf(tableName, "testTable%d", tableSize);
	//int t = 0;
	//memcpy(&t, src, 4);
	//printf("ocall writing %d to a file with %d bytes\n", t, dsize);fflush(stdout);
	FILE *outFile = fopen((char*)tableName, "a");
	fwrite(src, dsize, 1, outFile);
	fclose(outFile);
}

void ocall_read_file(void *dest, int dsize){
	if(readFile == NULL) printf("bad!!\n");
	//printf("b %d\n", dsize);
	int c = fread(dest, dsize, 1, readFile);
	//printf("c %d %d %d\n", c, ferror(readFile), feof(readFile));
	int t = 0;
	memcpy(&t, dest, 4);
	//printf("this funciton prints %d with %d bytes\n", t, dsize);
}

void
QueryFinishCallback(sgx_enclave_id_t enclave_id, int status)
{
	int i;
	// oblivStructureStorageTypes[newId] = MEMORY;
	for(i=0;i<NUM_STRUCTURES;++i){
		if(oblivStructureStorageTypes[i]==MEMORY) { break; }
	}
	// printf("ret table is %d\n", i);
	int rownum = oblivStructureSizes[i];
	uint8_t* addr = oblivStructures[i];
	Obliv_Type type = static_cast<Obliv_Type>(oblivStructureTypes[i]);
	size_t ATK_BLOCK_SIZE = getEncBlockSize(type);
	/* 唯一的一张 memory 表就是我们当前的结果 */
	// user logic to ret table

	// for example
	// print
	for(int j=0;j<rownum;++j){
		decryptOneBlock(
			enclave_id, (int*)&status, (Encrypted_Linear_Scan_Block*)(addr + j*ATK_BLOCK_SIZE), i);
	}

	// to disk

	return;
}

void
QueryFinish(
	char* tbname, 
	sgx_enclave_id_t enclave_id, int status, 
	void (*QueryCallback)(sgx_enclave_id_t, int))
{
	QueryCallback(enclave_id, status);
	return;
}

/**
 *****************************
 */
/**
 * just an example
 */
void
SelectTable(sgx_enclave_id_t enclave_id, int status)
{
	// CrackTables(enclave_id, status);
	// return;
	// oblidbextraio::DBTable* dbtables[NUM_STRUCTURES] = {nullptr};
	int i;
	std::string tbname;
	for(i=0;i<NUM_STRUCTURES;++i){
		if(!dbtables[i]) { continue; }
		oblidbextraio::DBTable* p = dbtables[i];
		tbname = p->TableName();
		std::cout << tbname << std::endl;
	}

	// 总共有几个 88
	char* name = const_cast<char *>(tbname.c_str());
	int low = 10, high = 13, lower = 9, higher = 14;

    Condition cond;
    cond.numClauses = 2;
    cond.fieldNums[0] = 3;
    cond.fieldNums[1] = 3;
    cond.conditionType[0] = 1;  // 1 means larger
    cond.conditionType[1] = -1;  // -1 means less than
    cond.values[0] = (uint8_t*)&lower;
    cond.values[1] = (uint8_t*)&higher;
    cond.nextCondition = NULL;

    // selectRows(
    //     enclave_id, 
    //     (int*)&status, 
    //     name, -1, cond, -1, -1, 1, 0); //continuous

    selectRows(
        enclave_id, 
        (int*)&status, 
        name, 3, cond, 0, -1, 1, 0); //continuous

	// 结果表已经写完了，select后面直接带一个函数算了，模拟一下回调
	QueryFinish(name, enclave_id, status, QueryFinishCallback);

    printf("Query over!\n");
	return;
}

/**
 * db open
 */
void
OpenDB1thTable(sgx_enclave_id_t enclave_id, int status)
{
	return;  // for test

	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	int structureId1 = -1;

    // 把表创建出来
	Schema rankingsSchema;
	rankingsSchema.numFields = 4;
	rankingsSchema.fieldOffsets[0] = 0;
	rankingsSchema.fieldSizes[0] = 1;
	rankingsSchema.fieldTypes[0] = CHAR;
	rankingsSchema.fieldOffsets[1] = 1;
	rankingsSchema.fieldSizes[1] = 255;
	rankingsSchema.fieldTypes[1] = TINYTEXT;
	rankingsSchema.fieldOffsets[2] = 256;
	rankingsSchema.fieldSizes[2] = 4;
	rankingsSchema.fieldTypes[2] = INTEGER;
	rankingsSchema.fieldOffsets[3] = 260;
	rankingsSchema.fieldSizes[3] = 4;
	rankingsSchema.fieldTypes[3] = INTEGER;

	if(rankingsSchema.numFields>NUM_STRUCTURES){
		printf("too mant fileds in table\n");
		exit(-1);
	}

	int rowline = 36;
    char* tableName = "testdbowc"; // open write close
	if(strlen(tableName)>=TABLE_NAME_LEN_MAX){
		printf("table name is too long\n");
		exit(-1);
	}
	globaltablename = tableName;
	globalschema = &rankingsSchema;

    createTable(
        enclave_id, 
        (int*)&status, 
        &rankingsSchema, 
        tableName, 
        strlen(tableName), 
        TYPE_LINEAR_SCAN, 
        rowline,
        &structureId1
    );

	globaltablename = nullptr;
	globalschema = nullptr;

	std::ifstream file("orderd.csv");
	char line[BLOCK_DATA_SIZE];//make this big just in case
	char data[BLOCK_DATA_SIZE];
	//file.getline(line, BLOCK_DATA_SIZE);//burn first line
	row[0] = 'a';
	for(int i = 0; i < rowline; i++){
		memset(row, 'a', BLOCK_DATA_SIZE);
		file.getline(line, BLOCK_DATA_SIZE);

		std::istringstream ss(line);
		for(int j = 0; j < 3; j++){
			if(!ss.getline(data, BLOCK_DATA_SIZE, ',')){break;}
			if(j == 1 || j == 2){
				int d = 0;
				d = atoi(data);
				memcpy(&row[rankingsSchema.fieldOffsets[j+1]], &d, 4);
			}
			else{
				strncpy((char*)&row[rankingsSchema.fieldOffsets[j+1]], data, strlen(data)+1);
			}
		}

		/**
		 * manually insert into the linear scan structure for speed purposes
		 * 这个函数都是 sgx 外部写，sgx 内部读
		 */
		opOneLinearScanBlock(enclave_id, (int*)&status, structureId1, i, (Linear_Scan_Block*)row, 1);
		incrementNumRows(enclave_id, (int*)&status, structureId1);
	}
	printf("Created DBContinueAT table\n");

	// table 创建完成之后 flush 一下
	storageengine->buffer_pool_manager_->FlushAllDirtyPage();

	// just 测试一下 db 的开关过程
	// CloseDB();
	// ConnectDB();

	/**
	 * 暴力读取并解密
	 */
	CrackTables(enclave_id, status);
	return;
}

void
PersistExample(sgx_enclave_id_t enclave_id, int status)
{
	return;
	// 开第二张表测试一下
	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	int tableid = -1;

    // 把表创建出来
	Schema rankingsSchema;
	rankingsSchema.numFields = 4;
	rankingsSchema.fieldOffsets[0] = 0;
	rankingsSchema.fieldSizes[0] = 1;
	rankingsSchema.fieldTypes[0] = CHAR;
	rankingsSchema.fieldOffsets[1] = 1;
	rankingsSchema.fieldSizes[1] = 255;
	rankingsSchema.fieldTypes[1] = TINYTEXT;
	rankingsSchema.fieldOffsets[2] = 256;
	rankingsSchema.fieldSizes[2] = 4;
	rankingsSchema.fieldTypes[2] = INTEGER;
	rankingsSchema.fieldOffsets[3] = 260;
	rankingsSchema.fieldSizes[3] = 4;
	rankingsSchema.fieldTypes[3] = INTEGER;

	if(rankingsSchema.numFields>NUM_STRUCTURES){
		printf("too mant fileds in table\n");
		exit(-1);
	}

	int rowline = 88;
    char* tableName = "test2th"; // open write close
	if(strlen(tableName)>=TABLE_NAME_LEN_MAX){
		printf("table name is too long\n");
		exit(-1);
	}
	globaltablename = tableName;
	globalschema = &rankingsSchema;

    createTable(
        enclave_id, 
        (int*)&status, 
        &rankingsSchema, 
        tableName, 
        strlen(tableName), 
        TYPE_LINEAR_SCAN, 
        rowline,
        &tableid
    );

	globaltablename = nullptr;
	globalschema = nullptr;

	std::ifstream file("orderd.csv");  // 输入文件流对象 file, input file
	char line[BLOCK_DATA_SIZE];
	char data[BLOCK_DATA_SIZE];
	row[0] = 'a';
	for(int i = 0; i < rowline; i++){
		memset(row, 'a', BLOCK_DATA_SIZE);
		file.getline(line, BLOCK_DATA_SIZE);  // 从文件流中读取 512 字节内容，读够511个字符 或 遇到 \n 提前结束，这里基本都读到 \n 然后提前结束了

		std::istringstream ss(line);  // 再把 line 变成一个字符串流 同样是 input 流
		for(int j = 0; j < 3; j++){
			if(!ss.getline(data, BLOCK_DATA_SIZE, ',')){break;}
			if(j == 1 || j == 2){
				int d = 0;
				d = atoi(data);
				memcpy(&row[rankingsSchema.fieldOffsets[j+1]], &d, 4);
			}
			else{
				strncpy((char*)&row[rankingsSchema.fieldOffsets[j+1]], data, strlen(data)+1);
			}
		}

		opOneLinearScanBlock(enclave_id, (int*)&status, tableid, i, (Linear_Scan_Block*)row, 1);
		incrementNumRows(enclave_id, (int*)&status, tableid);
	}
	printf("Created 2th table\n");

	storageengine->buffer_pool_manager_->FlushAllDirtyPage();

	return;
}

/**
 * 攻击oblidb continue 的 query, 以获取 range 在 orderd 表中的位置
 */
void
DBContinueAT(sgx_enclave_id_t enclave_id, int status)
{
	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);

	int structureId1 = -1;
	int structureId2 = -1;

    // 把表创建出来
	Schema rankingsSchema;
	rankingsSchema.numFields = 4;
	rankingsSchema.fieldOffsets[0] = 0;
	rankingsSchema.fieldSizes[0] = 1;
	rankingsSchema.fieldTypes[0] = CHAR;
	rankingsSchema.fieldOffsets[1] = 1;
	rankingsSchema.fieldSizes[1] = 255;
	rankingsSchema.fieldTypes[1] = TINYTEXT;
	rankingsSchema.fieldOffsets[2] = 256;
	rankingsSchema.fieldSizes[2] = 4;
	rankingsSchema.fieldTypes[2] = INTEGER;
	rankingsSchema.fieldOffsets[3] = 260;
	rankingsSchema.fieldSizes[3] = 4;
	rankingsSchema.fieldTypes[3] = INTEGER;

	int real_rowline = 36; //360000;

    // 这里要搞一个范围查询, 该表中第三列的值有 1-360000
    // int low = 3787, high = 68361;  // 随机的查询范围 begin end
    // int lower = 3786, higher = 68362;

	// for debug
	int low = 10, high = 13, lower = 9, higher = 14;  // 36
	// int low = 100, high = 190, lower = 99, higher = 191;  // 360
	// int low = 120, high = 3229, lower = 119, higher = 3230;  // 3600

    Condition cond;

    // Clauses 条款
    cond.numClauses = 2;
    // fieldNums 应该指的是列号
    cond.fieldNums[0] = 3;
    cond.fieldNums[1] = 3;
    cond.conditionType[0] = 1;  // 1 means larger
    cond.conditionType[1] = -1;  // -1 means less than
    cond.values[0] = (uint8_t*)&lower;
    cond.values[1] = (uint8_t*)&higher;
    cond.nextCondition = NULL;

	// 	case TYPE_LINEAR_SCAN:
	//		encBlockSize = sizeof(Encrypted_Linear_Scan_Block);

    char* tableName = "orderd";
    createTable(
        enclave_id, 
        (int*)&status, 
        &rankingsSchema, 
        tableName, 
        strlen(tableName), 
        TYPE_LINEAR_SCAN, 
        real_rowline,
        &structureId1
    );//TODO temp really 360010

	return;

	std::ifstream file("orderd.csv");

	char line[BLOCK_DATA_SIZE];//make this big just in case
	char data[BLOCK_DATA_SIZE];
	//file.getline(line, BLOCK_DATA_SIZE);//burn first line
	row[0] = 'a';
	for(int i = 0; i < real_rowline; i++){
		memset(row, 'a', BLOCK_DATA_SIZE);
		file.getline(line, BLOCK_DATA_SIZE);

		std::istringstream ss(line);
		for(int j = 0; j < 3; j++){
			if(!ss.getline(data, BLOCK_DATA_SIZE, ',')){break;}
			if(j == 1 || j == 2){//integer
				int d = 0;
				d = atoi(data);
				memcpy(&row[rankingsSchema.fieldOffsets[j+1]], &d, 4);
			}
			else{//tinytext
				strncpy((char*)&row[rankingsSchema.fieldOffsets[j+1]], data, strlen(data)+1);
			}
		}

		//manually insert into the linear scan structure for speed purposes
		opOneLinearScanBlock(enclave_id, (int*)&status, structureId1, i, (Linear_Scan_Block*)row, 1);
		incrementNumRows(enclave_id, (int*)&status, structureId1);
	}
	printf("Created DBContinueAT table\n");
	return;

	Obliv_Type _type = static_cast<Obliv_Type>(oblivStructureTypes[structureId1]);
    size_t ATK_BLOCK_SIZE = getEncBlockSize(_type);
	char tmparray[ATK_BLOCK_SIZE];

	int ttableid = structureId1;
	// 完整的input表
    uint8_t* Ttable = (uint8_t*)oblivStructures[ttableid];
	size_t T = real_rowline;  // 360000

	/**
	 * debug 测试一下内存中的value能否再读回来
	 */
	// std::fstream sgx_db_io_;
	// std::string sgxname("testsgx.dat");

	// sgx_db_io_.open(sgxname, std::ios::binary | std::ios::in | std::ios::out);
    // // directory or file does not exist
    // if (!sgx_db_io_.is_open()) {
    //     sgx_db_io_.clear();
    //     // create a new file
    //     sgx_db_io_.open(sgxname, std::ios::binary | std::ios::trunc | std::ios::out);
    //     sgx_db_io_.close();
    //     // reopen with original mode
    //     sgx_db_io_.open(sgxname, std::ios::binary | std::ios::in | std::ios::out);
    // }

	// for(int _sgx=0;_sgx<T;++_sgx){
	// 	size_t _offset = _sgx*ATK_BLOCK_SIZE;
	// 	char* _sgxt = reinterpret_cast<char *>(Ttable + _offset);
	// 	memcpy((void *)tmparray, (void *)_sgxt, ATK_BLOCK_SIZE);
	// 	// std::string ___sgxt;
	// 	// // 这样来保存密文是没有什么问题的，后面看下解决方案
	// 	// for(int st=0;st<ATK_BLOCK_SIZE;++st){___sgxt.push_back(tmparray[st]);
	// 	// sgx_db_io_.seekp(_offset);
	// 	sgx_db_io_.write(_sgxt, ATK_BLOCK_SIZE);
	// }
	// sgx_db_io_.sync();

	// for(int _sgx=0;_sgx<T;++_sgx){
	// 	size_t _offset = _sgx*ATK_BLOCK_SIZE;
	// 	sgx_db_io_.seekp(_offset);
	// 	sgx_db_io_.read(tmparray, ATK_BLOCK_SIZE);
	// 	decryptOneBlock(enclave_id, (int*)&status, (Encrypted_Linear_Scan_Block*)tmparray, 0);
	// }
	// sgx_db_io_.close();

	// 尝试读回来
	// std::ifstream sgxfile("testsgx.dat");
	// for(int i = 0; i < real_rowline; i++){
	// 	sgxfile.getline(tmparray, ATK_BLOCK_SIZE);
	// 	decryptOneBlock(enclave_id, (int*)&status, (Encrypted_Linear_Scan_Block*)tmparray, 0);
	// }
	// return;  // 测试一下写下去还能不能再读回来

    /**
     * the 4th para, if colChoice = -1, select all columns
     * the 8th means continuous
     */
    selectRows(
        enclave_id, 
        (int*)&status, 
        "orderd", -1, cond, -1, -1, 1, 0); //continuous
    
    printf("Query over, Start cracked!\n");

    // 找到原表与原结果表，原表与结果表的大小算已知条件
    
    int rtableid = 1;

    // low = 3787, high = 68361
    attacker::OblidbContinueAttackTest test(low, high);

    size_t R = test.Size();
    size_t STEP = R;
    
    size_t RANGE_LOW = test.Begin();
    size_t RANGE_HIGH = test.End();

    assert(R==oblivStructureSizes[rtableid]);

	// 完整的output表, 重新分配，因为结果表的这部分会被清理掉，驻留在 sgx 之外
    // uint8_t* Rtable = (uint8_t*)malloc(ATK_BLOCK_SIZE*oblivStructureSizes[rtableid]);  // about 35 M
	// memcpy((void *)Rtable, (void *)oblivStructures[rtableid], ATK_BLOCK_SIZE*oblivStructureSizes[rtableid]);
	printf(
		"Return table id: %d, addr of return table: %p, size: %d\n", 
		rtableid, oblivStructures[rtableid], ATK_BLOCK_SIZE*oblivStructureSizes[rtableid]);

	// R表的结果可以写到set中，后面都直接用set去比完事, set 是有序的容器
	std::set<std::string> Rtable;
	std::set<std::string> tmpRtable;
	for(int _ii=0;_ii<R;++_ii){
		char* _srcv = reinterpret_cast<char *>(oblivStructures[rtableid] + _ii*ATK_BLOCK_SIZE);
		memcpy((void *)tmparray, (void *)_srcv, ATK_BLOCK_SIZE);
		// decryptOneBlock(enclave_id, (int*)&status, (Encrypted_Linear_Scan_Block*)tmparray, 0);
		// std::string __srcv(_srcv);  // char* 是 \0 结束的，std::string 相当于是容器，不是以 \0 为结束符的
		std::string __srcv;
		// 这样来保存密文是没有什么问题的，后面看下解决方案
		for(int st=0;st<ATK_BLOCK_SIZE;++st){__srcv.push_back(tmparray[st]);}
		Rtable.insert(__srcv);
		// __srcv.copy(tmparray, ATK_BLOCK_SIZE, 0);
		// std::cout << __srcv.length() << std::endl;
		// decryptOneBlock(enclave_id, (int*)&status, (Encrypted_Linear_Scan_Block*)__srcv.c_str(), 0);
	}
	// for(auto a=Rtable.begin();a!=Rtable.end();++a){
	// 	decryptOneBlock(enclave_id, (int*)&status, (Encrypted_Linear_Scan_Block*)((*a).c_str()), 0);
	// }

	/**
	 * 打印 T 表与 R 表，仅 debug 用，且数量较少
	 * continue 的结果表本身就不是排序的，是取模之后放到结果表中的，是有两段连续的过程
	 */
	// // debug T 表
	// printf("T table\n");
	// for(int _ii=0;_ii<T;++_ii){
	// 	char* srcv = reinterpret_cast<char *>(Ttable + _ii*ATK_BLOCK_SIZE);
	// 	decryptOneBlock(enclave_id, (int*)&status, (Encrypted_Linear_Scan_Block*)srcv, 0);
	// }
	// // debug R 表
	// printf("R table\n");
	// for(int _jj=0;_jj<R;++_jj){
	// 	char* dstv = reinterpret_cast<char *>(oblivStructures[rtableid] + _jj*ATK_BLOCK_SIZE);
	// 	decryptOneBlock(enclave_id, (int*)&status, (Encrypted_Linear_Scan_Block*)dstv, 0);
	// }
	// return;

    // copy 返回表之后删除返回表
    deleteTable(enclave_id, (int*)&status, "ReturnTable");

    size_t lowindx = RANGE_LOW - 1;
    size_t upindex = RANGE_HIGH;

    std::cout 
        << "Finish the building of T and R" << std::endl
        << "    Begin in T:" << lowindx << "    we will crack it" << std::endl
        << "    R:" << R << std::endl
        << "    T:" << T << std::endl
        << "    ATK_BLOCK_SIZE:" << ATK_BLOCK_SIZE << std::endl
        << "    RANGE_LOW: " << RANGE_LOW << std::endl
        << "    RANGE_HIGH: " << RANGE_HIGH << std::endl;


    // 创建临时表，将原表重排序后输入, 重排序的过程无需进入sgx，在sgx外完成copy就可以了
    // id 应该是 2
    char* reordertableName = "reorderd";
    createTable(
        enclave_id, 
        (int*)&status, 
        &rankingsSchema, 
        reordertableName, 
        strlen(reordertableName), 
        TYPE_LINEAR_SCAN, 
        real_rowline,
        &structureId2
    );

    uint8_t* tmpttable = (uint8_t*)oblivStructures[structureId2];
    assert(1==structureId2);

    // TODO 参数传的乱，先写一个长函数吧
    attacker::cursor _cursor;
    _cursor.begin = 0;
    _cursor.whichloop = 0;

    uint64_t rollbackbegin;
    uint64_t reorderend;
    void* reorderdst;
	void* reordersrc;
	bool same;
	char* dstv;  // 原表
	char* srcv;  // 临时表

    while(STEP)
	{
		/**
		 * gen reorder table
		 */
		// 这里的j不一定要由0开始，可以利用之前得到的结果优化，少一些循环
        // for(int j=_cursor.whichloop;j<T;++j)
		for(int j=_cursor.whichloop;j<T;++j)
        {
			/**
			 * 临时表地址 tmpttable，它的数据来源于乱序后的 input 表，直接copy就可以了
			 * query 乱序表的时候再进入sgx即可
			 * 理想很美好，但是现实很骨感，还是需要用进入到sgx去写，否则有一个地址的校验不过
			 * 但是调整顺序之后，再次写到sgx之外的空间还会有问题，与原内容已经不一致了
			 * 很难再次使用 oblidb 的 query 方法，所以说服力会少一点
			 * 加密的块中同时保存了 这个 tuple 应该的行号以及 版本号，这个直接乱序表再去 apply 是有问题的
			 */
            reorderend = static_cast<uint64_t>((j + STEP) % T);

            if(j > reorderend){
                for(int index=0;index<T;++index)
				{
					reordersrc = reinterpret_cast<void *>((Ttable + index*ATK_BLOCK_SIZE));

                    if(index < reorderend){ // 采样数据, 在table的最末端
                        reorderdst = \
							reinterpret_cast<void *>((tmpttable + (T-reorderend+index)*ATK_BLOCK_SIZE));
                    } else if (index>=reorderend && index<j){ // 整体前移的数据
                        reorderdst = \
							reinterpret_cast<void *>((tmpttable + (index-reorderend)*ATK_BLOCK_SIZE));
                    } else { // 采样数据
                        reorderdst = \
							reinterpret_cast<void *>((tmpttable + (index-reorderend)*ATK_BLOCK_SIZE));
                    }

					memcpy(reorderdst, reordersrc, ATK_BLOCK_SIZE);
                }
            } else {
				for(int index=0;index<T;++index)
				{
					reordersrc = reinterpret_cast<void *>((Ttable + index*ATK_BLOCK_SIZE));

					if(index < j){
						reorderdst = reinterpret_cast<void *>((tmpttable + index*ATK_BLOCK_SIZE));
					} else if (index >= j && index < reorderend){
						reorderdst = reinterpret_cast<void *>((tmpttable + (T-STEP+index-j)*ATK_BLOCK_SIZE));
					} else {
						reorderdst = reinterpret_cast<void *>((tmpttable + (index-STEP)*ATK_BLOCK_SIZE));
					}

					memcpy(reorderdst, reordersrc, ATK_BLOCK_SIZE);
				}
            }

			/**
			 * apply the same query to reorderd table
			 * the id of new return table (r temp table) should be 2
			 * 
			 * 硕哥说的攻击方式，尝试一下按照实际形式去存取
			 */
			selectRows(
				enclave_id, (int*)&status, "reorderd", -1, cond, -1, -1, 1, 0); // 8th para means continuous
			// return;

			same = true;
			// printf("first query,%d\n",oblivStructureSizes[2]);
			// printf("R is %d\n", R);  // 64575
			/**
			 * 之前的比较算法包含了对顺序的约束，认为只要顺序不一致，就不一样，但是并非如此
			 * 结果表本身就不是按顺序的，但是会漏值
			 * 所以比较的时候就比较考验算法了
			 * 以标准的为基准，就是最简单的2重循环，这个必然是不可以的，参考一下LeetCode的第一题，可以用空间开销来换
			 */
			// for(int ii=0;ii<R;++ii){
			// 	char* srcv = reinterpret_cast<char *>(Rtable + ii*ATK_BLOCK_SIZE);
			// 	char* dstv = reinterpret_cast<char *>(oblivStructures[2] + ii*ATK_BLOCK_SIZE);
			// 	std::string _dstv(dstv);
			// 	std::string _srcv(srcv);

			// 	// std::cout << "dst: " << _dstv << " " << "src: " << _srcv << std::endl;
			// 	decryptOneBlock(enclave_id, (int*)&status, (Encrypted_Linear_Scan_Block*)srcv, 1);
			// 	decryptOneBlock(enclave_id, (int*)&status, (Encrypted_Linear_Scan_Block*)dstv, 2);
			// 	// return;

			// 	// if(_dstv.compare(_srcv) != 0){
			// 	// 	same = false;
			// 	// 	break;
			// 	// }
			// }
			tmpRtable.clear();
			for(int _ii=0;_ii<R;++_ii){
				char* _srcv = reinterpret_cast<char *>(oblivStructures[2] + _ii*ATK_BLOCK_SIZE);
				memcpy((void *)tmparray, (void *)_srcv, ATK_BLOCK_SIZE);
				std::string __srcv;
				// 这样来保存密文是没有什么问题的，后面看下解决方案
				for(int st=0;st<ATK_BLOCK_SIZE;++st){__srcv.push_back(tmparray[st]);}
				tmpRtable.insert(__srcv);
				// decryptOneBlock(enclave_id, (int*)&status, (Encrypted_Linear_Scan_Block*)__srcv.c_str(), 0);
			}

			// // set 均为有序的集合，直接按照顺序容器的方式去比较即可
			// for(auto rt=Rtable.begin(), trt=tmpRtable.begin();rt!=Rtable.end(); ++rt, ++trt){
			// 	same = sgxCompareBlock(
			// 		enclave_id, (int*)&status, (Encrypted_Linear_Scan_Block*)__srcv.c_str(), (Encrypted_Linear_Scan_Block*)__srcv.c_str())
			// }
			if(oblivStructureQueryTypes[2]!=88){
				printf("Querytype:%d\n", oblivStructureQueryTypes[2]);
				same = false;
			}
			oblivStructureQueryTypes[2]=0;
			/**
			 * after compare, if equal, break and out, the returntable must be deleted
			 */
			deleteTable(enclave_id, (int*)&status, "ReturnTable");

			// printf("STEP=%d, J=%d\n", STEP, j);
			if(!same){
				_cursor.begin = 0;  // 常规算法实现中，这里应该是 select 的返回值，是不会泄露到sgx之外的，真实用例中，这个东西是没有用的
				_cursor.whichloop = j;
				// printf("	Different\n");
				break;
			}
        }  // in a loop, every time of the loop, a new r table generated

        printf(
            "KEY OUT, Step:%d, Loop index:%d\n", 
            STEP, _cursor.whichloop);
        STEP /= 2;
    }

    deleteTable(enclave_id, (int*)&status, "orderd");
    deleteTable(enclave_id, (int*)&status, "reorderd");

    return;
}

/**
 *****************************
 */


void BDB1Index(sgx_enclave_id_t enclave_id, int status){
	//block size needs to be 512

	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	int structureIdIndex = -1;
	int structureIdLinear = -1;
	Schema rankingsSchema;
	rankingsSchema.numFields = 4;
	rankingsSchema.fieldOffsets[0] = 0;
	rankingsSchema.fieldSizes[0] = 1;
	rankingsSchema.fieldTypes[0] = CHAR;
	rankingsSchema.fieldOffsets[1] = 1;
	rankingsSchema.fieldSizes[1] = 255;
	rankingsSchema.fieldTypes[1] = TINYTEXT;
	rankingsSchema.fieldOffsets[2] = 256;
	rankingsSchema.fieldSizes[2] = 4;
	rankingsSchema.fieldTypes[2] = INTEGER;
	rankingsSchema.fieldOffsets[3] = 260;
	rankingsSchema.fieldSizes[3] = 4;
	rankingsSchema.fieldTypes[3] = INTEGER;

	Condition cond;
	int val = 1000;
	cond.numClauses = 1;
	cond.fieldNums[0] = 2;
	cond.conditionType[0] = 1;
	cond.values[0] = (uint8_t*)malloc(4);
	memcpy(cond.values[0], &val, 4);
	cond.nextCondition = NULL;

	char* tableName = "rankings";
	createTable(enclave_id, (int*)&status, &rankingsSchema, tableName, strlen(tableName), TYPE_TREE_ORAM, 360010, &structureIdIndex);//TODO temp really 360010
	//printTable(enclave_id, (int*)&status, "rankings");

	std::ifstream file("rankings.csv");

	char line[BLOCK_DATA_SIZE];//make this big just in case
	char data[BLOCK_DATA_SIZE];
	//file.getline(line, BLOCK_DATA_SIZE);//burn first line
	row[0] = 'a';
	for(int i = 0; i < 360000; i++){//TODO temp really 360000
	//for(int i = 0; i < 1000; i++){
		memset(row, 'a', BLOCK_DATA_SIZE);
		file.getline(line, BLOCK_DATA_SIZE);//get the field

		std::istringstream ss(line);
		for(int j = 0; j < 3; j++){
			if(!ss.getline(data, BLOCK_DATA_SIZE, ',')){
				break;
			}
			//printf("data: %s\n", data);
			if(j == 1 || j == 2){//integer
				int d = 0;
				d = atoi(data);
				//printf("data: %s\n", data);
				//printf("d %d\n", d);
				memcpy(&row[rankingsSchema.fieldOffsets[j+1]], &d, 4);
			}
			else{//tinytext
				strncpy((char*)&row[rankingsSchema.fieldOffsets[j+1]], data, strlen(data)+1);
			}
		}
		//insert the row into the database - index by last sale price
		int indexval = 0;
		memcpy(&indexval, &row[rankingsSchema.fieldOffsets[2]], 4);
		insertIndexRowFast(enclave_id, (int*)&status, "rankings", row, indexval);
		//if (indexval > 1000) printf("indexval %d \n", indexval);
		//printTable(enclave_id, (int*)&status, "rankings");
	}

	printf("created BDB1 table\n");
	time_t startTime, endTime;
	double elapsedTime;
	//printTable(enclave_id, (int*)&status, "rankings");

	startTime = clock();
	indexSelect(enclave_id, (int*)&status, "rankings", -1, cond, -1, -1, 2, 1000, INT_MAX, 0);
	//char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice, int key_start, int key_end
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("BDB1 running time (small): %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
	startTime = clock();
	indexSelect(enclave_id, (int*)&status, "rankings", -1, cond, -1, -1, 3, 1000, INT_MAX, 0);
	//char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice, int key_start, int key_end
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("BDB1 running time (hash): %.5f\n", elapsedTime);
	printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
	startTime = clock();
	indexSelect(enclave_id, (int*)&status, "rankings", -1, cond, -1, -1, 5, 1000, INT_MAX, 0);
	//char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice, int key_start, int key_end
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("BDB1 running time (baseline): %.5f\n", elapsedTime);
	printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");

    deleteTable(enclave_id, (int*)&status, "rankings");
}

void BDB1Linear(sgx_enclave_id_t enclave_id, int status){
	//block size needs to be 512
	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	int structureId1 = -1;
	int structureId2 = -1;
	Schema rankingsSchema;
	rankingsSchema.numFields = 4;
	rankingsSchema.fieldOffsets[0] = 0;
	rankingsSchema.fieldSizes[0] = 1;
	rankingsSchema.fieldTypes[0] = CHAR;
	rankingsSchema.fieldOffsets[1] = 1;
	rankingsSchema.fieldSizes[1] = 255;
	rankingsSchema.fieldTypes[1] = TINYTEXT;
	rankingsSchema.fieldOffsets[2] = 256;
	rankingsSchema.fieldSizes[2] = 4;
	rankingsSchema.fieldTypes[2] = INTEGER;
	rankingsSchema.fieldOffsets[3] = 260;
	rankingsSchema.fieldSizes[3] = 4;
	rankingsSchema.fieldTypes[3] = INTEGER;

	Condition cond;
	int val = 1000;
	cond.numClauses = 1;
	cond.fieldNums[0] = 2;
	cond.conditionType[0] = 1;
	cond.values[0] = (uint8_t*)malloc(4);
	memcpy(cond.values[0], &val, 4);
	cond.nextCondition = NULL;

	// int real_rowline = 360000;
	int real_rowline = 360;

	char* tableName = "rankings";
	createTable(
		enclave_id, (int*)&status, 
		&rankingsSchema, tableName, 
		strlen(tableName), TYPE_LINEAR_SCAN, real_rowline + 10, &structureId1); //TODO temp really 360010

	std::ifstream file("rankings.csv");

	char line[BLOCK_DATA_SIZE];//make this big just in case
	char data[BLOCK_DATA_SIZE];
	//file.getline(line, BLOCK_DATA_SIZE);//burn first line
	row[0] = 'a';
	for(int i = 0; i < real_rowline; i++){ //TODO temp really real_rowline
	//for(int i = 0; i < 1000; i++){
		memset(row, 'a', BLOCK_DATA_SIZE);
		file.getline(line, BLOCK_DATA_SIZE);//get the field

		std::istringstream ss(line);
		for(int j = 0; j < 3; j++){
			if(!ss.getline(data, BLOCK_DATA_SIZE, ',')){
				break;
			}
			//printf("data: %s\n", data);
			if(j == 1 || j == 2){//integer
				int d = 0;
				d = atoi(data);
				//printf("data: %s\n", data);
				//printf("d %d\n", d);
				memcpy(&row[rankingsSchema.fieldOffsets[j+1]], &d, 4);
			}
			else{//tinytext
				strncpy((char*)&row[rankingsSchema.fieldOffsets[j+1]], data, strlen(data)+1);
			}
		}
		//manually insert into the linear scan structure for speed purposes
		opOneLinearScanBlock(enclave_id, (int*)&status, structureId1, i, (Linear_Scan_Block*)row, 1);
		incrementNumRows(enclave_id, (int*)&status, structureId1);
	}
	printf("created BDB1 table - linear\n");
	return;

	time_t startTime, endTime;
	double elapsedTime;
	//printTable(enclave_id, (int*)&status, "rankings");

	startTime = clock();
	// colChoice = -1 means select all col, no aggregate no groupCol
	selectRows(enclave_id, (int*)&status, "rankings", -1, cond, -1, -1, 2, 0);
	//char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice, int intermediate
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("BDB1 running time (small): %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
	startTime = clock();
	selectRows(enclave_id, (int*)&status, "rankings", -1, cond, -1, -1, 3, 0);
	//char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice, int intermediate
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("BDB1 running time (hash): %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
	startTime = clock();
	selectRows(enclave_id, (int*)&status, "rankings", -1, cond, -1, -1, 5, 0);
	//char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice, int key_start, int key_end
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("BDB1 running time (baseline): %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "rankings");
}


void BDB2(sgx_enclave_id_t enclave_id, int status, int baseline)
{
	//block size 2048

	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	int structureIdIndex = -1;
	int structureIdLinear = -1;
	Schema userdataSchema;
	userdataSchema.numFields = 10;
	userdataSchema.fieldOffsets[0] = 0;
	userdataSchema.fieldSizes[0] = 1;
	userdataSchema.fieldTypes[0] = CHAR;
	userdataSchema.fieldOffsets[1] = 1;
	userdataSchema.fieldSizes[1] = 255;
	userdataSchema.fieldTypes[1] = TINYTEXT;
	userdataSchema.fieldOffsets[2] = 256;
	userdataSchema.fieldSizes[2] = 255;
	userdataSchema.fieldTypes[2] = TINYTEXT;
	userdataSchema.fieldOffsets[3] = 511;
	userdataSchema.fieldSizes[3] = 4;
	userdataSchema.fieldTypes[3] = INTEGER;
	userdataSchema.fieldOffsets[4] = 515;
	userdataSchema.fieldSizes[4] = 4;
	userdataSchema.fieldTypes[4] = INTEGER;
	userdataSchema.fieldOffsets[5] = 519;
	userdataSchema.fieldSizes[5] = 255;
	userdataSchema.fieldTypes[5] = TINYTEXT;
	userdataSchema.fieldOffsets[6] = 774;
	userdataSchema.fieldSizes[6] = 255;
	userdataSchema.fieldTypes[6] = TINYTEXT;
	userdataSchema.fieldOffsets[7] = 1029;
	userdataSchema.fieldSizes[7] = 255;
	userdataSchema.fieldTypes[7] = TINYTEXT;
	userdataSchema.fieldOffsets[8] = 1284;
	userdataSchema.fieldSizes[8] = 255;
	userdataSchema.fieldTypes[8] = TINYTEXT;
	userdataSchema.fieldOffsets[9] = 1539;
	userdataSchema.fieldSizes[9] = 4;
	userdataSchema.fieldTypes[9] = INTEGER;

	Condition cond;
	cond.numClauses = 0;
	cond.nextCondition = NULL;

	char* tableName = "uservisits";
	createTable(enclave_id, (int*)&status, &userdataSchema, tableName, strlen(tableName), TYPE_LINEAR_SCAN, 350010, &structureIdLinear);//TODO temp really 350010

	std::ifstream file2("uservisits.csv");
	char line[BLOCK_DATA_SIZE];//make this big just in case
	char data[BLOCK_DATA_SIZE];
	//file.getline(line, BLOCK_DATA_SIZE);//burn first line
	row[0] = 'a';
	for(int i = 0; i < 350000; i++){//TODO temp really 350000
	//for(int i = 0; i < 1000; i++){
		memset(row, 'a', BLOCK_DATA_SIZE);
		file2.getline(line, BLOCK_DATA_SIZE);//get the field

		std::istringstream ss(line);
		for(int j = 0; j < 9; j++){
			if(!ss.getline(data, BLOCK_DATA_SIZE, ',')){
				break;
			}
			//printf("data: %s\n", data);
			if(j == 2 || j == 3 || j == 8){//integer
				int d = 0;
				if(j==3) d = atof(data)*100;
				else d = atoi(data);
				//printf("data: %s\n", data);
				//printf("d %d ", d);
				memcpy(&row[userdataSchema.fieldOffsets[j+1]], &d, 4);
			}
			else{//tinytext
				strncpy((char*)&row[userdataSchema.fieldOffsets[j+1]], data, strlen(data)+1);
			}
		}
		//manually insert into the linear scan structure for speed purposes
		opOneLinearScanBlock(enclave_id, (int*)&status, structureIdLinear, i, (Linear_Scan_Block*)row, 1);
		incrementNumRows(enclave_id, (int*)&status, structureIdLinear);
	}

	printf("created BDB2 table\n");
	time_t startTime, endTime;
	double elapsedTime;
	//printTable(enclave_id, (int*)&status, "uservisits");
	startTime = clock();
	if(baseline == 1)
		selectRows(enclave_id, (int*)&status, "uservisits", 4, cond, 1, 1, -2, 2);
	else
		highCardLinGroupBy(enclave_id, (int*)&status, "uservisits", 4, cond, 1, 1, -2, 0);
	//char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	//printf("BDB2 running time: %.5f\n", elapsedTime);
	printTable(enclave_id, (int*)&status, "ReturnTable");
	printf("BDB2 running time: %.5f\n", elapsedTime);

    deleteTable(enclave_id, (int*)&status, "ReturnTable");

    deleteTable(enclave_id, (int*)&status, "uservisits");
}

void BDB2Index(sgx_enclave_id_t enclave_id, int status, int baseline){
//block size 2048

	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	int structureIdIndex = -1;
	int structureIdLinear = -1;
	Schema userdataSchema;
	userdataSchema.numFields = 10;
	userdataSchema.fieldOffsets[0] = 0;
	userdataSchema.fieldSizes[0] = 1;
	userdataSchema.fieldTypes[0] = CHAR;
	userdataSchema.fieldOffsets[1] = 1;
	userdataSchema.fieldSizes[1] = 255;
	userdataSchema.fieldTypes[1] = TINYTEXT;
	userdataSchema.fieldOffsets[2] = 256;
	userdataSchema.fieldSizes[2] = 255;
	userdataSchema.fieldTypes[2] = TINYTEXT;
	userdataSchema.fieldOffsets[3] = 511;
	userdataSchema.fieldSizes[3] = 4;
	userdataSchema.fieldTypes[3] = INTEGER;
	userdataSchema.fieldOffsets[4] = 515;
	userdataSchema.fieldSizes[4] = 4;
	userdataSchema.fieldTypes[4] = INTEGER;
	userdataSchema.fieldOffsets[5] = 519;
	userdataSchema.fieldSizes[5] = 255;
	userdataSchema.fieldTypes[5] = TINYTEXT;
	userdataSchema.fieldOffsets[6] = 774;
	userdataSchema.fieldSizes[6] = 255;
	userdataSchema.fieldTypes[6] = TINYTEXT;
	userdataSchema.fieldOffsets[7] = 1029;
	userdataSchema.fieldSizes[7] = 255;
	userdataSchema.fieldTypes[7] = TINYTEXT;
	userdataSchema.fieldOffsets[8] = 1284;
	userdataSchema.fieldSizes[8] = 255;
	userdataSchema.fieldTypes[8] = TINYTEXT;
	userdataSchema.fieldOffsets[9] = 1539;
	userdataSchema.fieldSizes[9] = 4;
	userdataSchema.fieldTypes[9] = INTEGER;

	Condition cond;
	cond.numClauses = 0;
	cond.nextCondition = NULL;

	char* tableName = "uservisits";
	createTable(enclave_id, (int*)&status, &userdataSchema, tableName, strlen(tableName), TYPE_TREE_ORAM, 350010, &structureIdIndex);//TODO temp really 350010


	std::ifstream file2("uservisits.csv");
	char line[BLOCK_DATA_SIZE];//make this big just in case
	char data[BLOCK_DATA_SIZE];
	//file.getline(line, BLOCK_DATA_SIZE);//burn first line
	row[0] = 'a';
	for(int i = 0; i < 350000; i++){//TODO temp really 350000
	//for(int i = 0; i < 1000; i++){
		memset(row, 'a', BLOCK_DATA_SIZE);
		file2.getline(line, BLOCK_DATA_SIZE);//get the field

		std::istringstream ss(line);
		for(int j = 0; j < 9; j++){
			if(!ss.getline(data, BLOCK_DATA_SIZE, ',')){
				break;
			}
			//printf("data: %s\n", data);
			if(j == 2 || j == 3 || j == 8){//integer
				int d = 0;
				if(j==3) d = atof(data)*100;
				else d = atoi(data);
				//printf("data: %s\n", data);
				//printf("d %d ", d);
				memcpy(&row[userdataSchema.fieldOffsets[j+1]], &d, 4);
			}
			else{//tinytext
				strncpy((char*)&row[userdataSchema.fieldOffsets[j+1]], data, strlen(data)+1);
			}
		}
		int indexval = 0;
		memcpy(&indexval, &row[userdataSchema.fieldOffsets[9]], 4); //doesn't matter the column for this, we're doing linear scans anyway
		insertIndexRowFast(enclave_id, (int*)&status, "uservisits", row, indexval);
	}

	printf("created BDB2 table\n");
	time_t startTime, endTime;
	double elapsedTime;
	//printTable(enclave_id, (int*)&status, "uservisits");
	startTime = clock();
	highCardLinGroupBy(enclave_id, (int*)&status, "uservisits", 4, cond, 1, 1, -2, 0);
	//char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	//printf("BDB2 running time: %.5f\n", elapsedTime);
	printf("BDB2 running time: %.5f\n", elapsedTime);
	printTable(enclave_id, (int*)&status, "ReturnTable");

    deleteTable(enclave_id, (int*)&status, "ReturnTable");

    deleteTable(enclave_id, (int*)&status, "uservisits");
}

void BDB3(sgx_enclave_id_t enclave_id, int status, int baseline){

//block size 2048
	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	int structureId1 = -1;
	int structureId2 = -1;
	Schema rankingsSchema;
	rankingsSchema.numFields = 4;
	rankingsSchema.fieldOffsets[0] = 0;
	rankingsSchema.fieldSizes[0] = 1;
	rankingsSchema.fieldTypes[0] = CHAR;
	rankingsSchema.fieldOffsets[1] = 1;
	rankingsSchema.fieldSizes[1] = 255;
	rankingsSchema.fieldTypes[1] = TINYTEXT;
	rankingsSchema.fieldOffsets[2] = 256;
	rankingsSchema.fieldSizes[2] = 4;
	rankingsSchema.fieldTypes[2] = INTEGER;
	rankingsSchema.fieldOffsets[3] = 260;
	rankingsSchema.fieldSizes[3] = 4;
	rankingsSchema.fieldTypes[3] = INTEGER;

	char* tableName = "rankings";
	createTable(enclave_id, (int*)&status, &rankingsSchema, tableName, strlen(tableName), TYPE_LINEAR_SCAN, 360010, &structureId1); //TODO temp really 360010

	std::ifstream file("rankings.csv");

	char line[BLOCK_DATA_SIZE];//make this big just in case
	char data[BLOCK_DATA_SIZE];
	//file.getline(line, BLOCK_DATA_SIZE);//burn first line
	row[0] = 'a';
	for(int i = 0; i < 360000; i++){ //TODO temp really 360000
	//for(int i = 0; i < 1000; i++){
		memset(row, 'a', BLOCK_DATA_SIZE);
		file.getline(line, BLOCK_DATA_SIZE);//get the field

		std::istringstream ss(line);
		for(int j = 0; j < 3; j++){
			if(!ss.getline(data, BLOCK_DATA_SIZE, ',')){
				break;
			}
			//printf("data: %s\n", data);
			if(j == 1 || j == 2){//integer
				int d = 0;
				d = atoi(data);
				//printf("data: %s\n", data);
				//printf("d %d\n", d);
				memcpy(&row[rankingsSchema.fieldOffsets[j+1]], &d, 4);
			}
			else{//tinytext
				strncpy((char*)&row[rankingsSchema.fieldOffsets[j+1]], data, strlen(data)+1);
			}
		}
		//manually insert into the linear scan structure for speed purposes
		opOneLinearScanBlock(enclave_id, (int*)&status, structureId1, i, (Linear_Scan_Block*)row, 1);
		incrementNumRows(enclave_id, (int*)&status, structureId1);
	}
	printf("created rankings table\n");

	Schema userdataSchema;
	userdataSchema.numFields = 10;
	userdataSchema.fieldOffsets[0] = 0;
	userdataSchema.fieldSizes[0] = 1;
	userdataSchema.fieldTypes[0] = CHAR;
	userdataSchema.fieldOffsets[1] = 1;
	userdataSchema.fieldSizes[1] = 255;
	userdataSchema.fieldTypes[1] = TINYTEXT;
	userdataSchema.fieldOffsets[2] = 256;
	userdataSchema.fieldSizes[2] = 255;
	userdataSchema.fieldTypes[2] = TINYTEXT;
	userdataSchema.fieldOffsets[3] = 511;
	userdataSchema.fieldSizes[3] = 4;
	userdataSchema.fieldTypes[3] = INTEGER;
	userdataSchema.fieldOffsets[4] = 515;
	userdataSchema.fieldSizes[4] = 4;
	userdataSchema.fieldTypes[4] = INTEGER;
	userdataSchema.fieldOffsets[5] = 519;
	userdataSchema.fieldSizes[5] = 255;
	userdataSchema.fieldTypes[5] = TINYTEXT;
	userdataSchema.fieldOffsets[6] = 774;
	userdataSchema.fieldSizes[6] = 255;
	userdataSchema.fieldTypes[6] = TINYTEXT;
	userdataSchema.fieldOffsets[7] = 1029;
	userdataSchema.fieldSizes[7] = 255;
	userdataSchema.fieldTypes[7] = TINYTEXT;
	userdataSchema.fieldOffsets[8] = 1284;
	userdataSchema.fieldSizes[8] = 255;
	userdataSchema.fieldTypes[8] = TINYTEXT;
	userdataSchema.fieldOffsets[9] = 1539;
	userdataSchema.fieldSizes[9] = 4;
	userdataSchema.fieldTypes[9] = INTEGER;

	Condition cond;
	cond.numClauses = 0;
	cond.nextCondition = NULL;

	char* tableName2 = "uservisits";
	createTable(enclave_id, (int*)&status, &userdataSchema, tableName2, strlen(tableName2), TYPE_LINEAR_SCAN, 350010, &structureId2); //TODO temp really 350010

	std::ifstream file2("uservisits.csv");

	//file.getline(line, BLOCK_DATA_SIZE);//burn first line
	row[0] = 'a';
	for(int i = 0; i < 350000; i++){//TODO temp really 350000
	//for(int i = 0; i < 1000; i++){
		memset(row, 'a', BLOCK_DATA_SIZE);
		file2.getline(line, BLOCK_DATA_SIZE);//get the field

		std::istringstream ss(line);
		for(int j = 0; j < 9; j++){
			if(!ss.getline(data, BLOCK_DATA_SIZE, ',')){
				break;
			}
			//printf("data: %s\n", data);
			if(j == 2 || j == 3 || j == 8){//integer
				int d = 0;
				if(j==3) d = atof(data)*100;
				else d = atoi(data);
				//printf("data: %s\n", data);
				//printf("d %d ", d);
				memcpy(&row[userdataSchema.fieldOffsets[j+1]], &d, 4);
			}
			else{//tinytext
				strncpy((char*)&row[userdataSchema.fieldOffsets[j+1]], data, strlen(data)+1);
			}
		}
		//manually insert into the linear scan structure for speed purposes
		opOneLinearScanBlock(enclave_id, (int*)&status, structureId2, i, (Linear_Scan_Block*)row, 1);
		incrementNumRows(enclave_id, (int*)&status, structureId2);
	}

	printf("created uservisits table\n");
	time_t startTime, endTime;
	double elapsedTime;

	Condition cond1, cond2;
	int l = 19800100, h = 19800402;
	cond1.numClauses = 1;
	cond1.fieldNums[0] = 3;
	cond1.conditionType[0] = 1;
	cond1.values[0] = (uint8_t*)malloc(4);
	memcpy(cond1.values[0], &l, 4);
	cond1.nextCondition = &cond2;
	cond2.numClauses = 1;
	cond2.fieldNums[0] = 3;
	cond2.conditionType[0] = 2;
	cond2.values[0] = (uint8_t*)malloc(4);
	memcpy(cond2.values[0], &h, 4);
	cond2.nextCondition = NULL;
	Condition noCond;
	noCond.numClauses = 0;
	noCond.nextCondition = NULL;

	startTime = clock();
	if(baseline == 1){
		selectRows(enclave_id, (int*)&status, "uservisits", -1, cond1, -1, -1, 5, 0);
		renameTable(enclave_id, (int*)&status, "ReturnTable", "uvJ");
		//printTable(enclave_id, (int*)&status, "uvJ");
		joinTables(enclave_id, (int*)&status, "uvJ", "rankings",  2, 1, -1, -1);
		//int joinTables(char* tableName1, char* tableName2, int joinCol1, int joinCol2, int startKey, int endKey) {//put the smaller table first for
		renameTable(enclave_id, (int*)&status, "JoinReturn", "jr");
		//printTable(enclave_id, (int*)&status, "jr");
		selectRows(enclave_id, (int*)&status, "jr", 10, noCond, 4, 1, 4, 2);
		renameTable(enclave_id, (int*)&status, "ReturnTable", "last");
		//printTable(enclave_id, (int*)&status, "last");
		selectRows(enclave_id, (int*)&status, "last", 2, noCond, 3, -1, 0, 0);
	}
	else{
		selectRows(enclave_id, (int*)&status, "uservisits", -1, cond1, -1, -1, 2, 0);
		//indexSelect(enclave_id, (int*)&status, "uservisits", -1, cond1, -1, -1, 2, l, h);
		renameTable(enclave_id, (int*)&status, "ReturnTable", "uvJ");
		//printTable(enclave_id, (int*)&status, "uvJ");
		joinTables(enclave_id, (int*)&status, "uvJ", "rankings",  2, 1, -1, -1);
		//int joinTables(char* tableName1, char* tableName2, int joinCol1, int joinCol2, int startKey, int endKey) {//put the smaller table first for
		renameTable(enclave_id, (int*)&status, "JoinReturn", "jr");
		//printTable(enclave_id, (int*)&status, "jr");
		selectRows(enclave_id, (int*)&status, "jr", 10, noCond, 4, 1, 4, 0);
		renameTable(enclave_id, (int*)&status, "ReturnTable", "last");
		//printTable(enclave_id, (int*)&status, "last");
		selectRows(enclave_id, (int*)&status, "last", 2, noCond, 3, -1, -1, 0);
		//select from index
		//join
		//fancy group by
		//select max
		//char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice
	}
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("BDB3 running time: %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");

    deleteTable(enclave_id, (int*)&status, "uservisits");
    deleteTable(enclave_id, (int*)&status, "rankings");

}



void flightTables(sgx_enclave_id_t enclave_id, int status){
	//block data size can be shrunk as low as 32 for this test
//create a linear scan table and an index for the flight test data. Index the data by price
	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	int structureIdIndex = -1;
	int structureIdLinear = -1;
	Schema flightSchema;
	flightSchema.numFields = 8;
	flightSchema.fieldOffsets[0] = 0;
	flightSchema.fieldSizes[0] = 1;
	flightSchema.fieldTypes[0] = CHAR;
	flightSchema.fieldOffsets[1] = 1;
	flightSchema.fieldSizes[1] = 4;
	flightSchema.fieldTypes[1] = INTEGER;
	flightSchema.fieldOffsets[2] = 5;
	flightSchema.fieldSizes[2] = 4;
	flightSchema.fieldTypes[2] = INTEGER;
	flightSchema.fieldOffsets[3] = 9;
	flightSchema.fieldSizes[3] = 4;
	flightSchema.fieldTypes[3] = INTEGER;
	flightSchema.fieldOffsets[4] = 13;
	flightSchema.fieldSizes[4] = 4;
	flightSchema.fieldTypes[4] = INTEGER;
	flightSchema.fieldOffsets[5] = 17;
	flightSchema.fieldSizes[5] = 4;
	flightSchema.fieldTypes[5] = INTEGER;
	flightSchema.fieldOffsets[6] = 21;
	flightSchema.fieldSizes[6] = 4;
	flightSchema.fieldTypes[6] = INTEGER;
	flightSchema.fieldOffsets[7] = 25;
	flightSchema.fieldSizes[7] = 4;
	flightSchema.fieldTypes[7] = INTEGER;

	Condition cond0;
	int val = 12173;
	cond0.numClauses = 1;
	cond0.fieldNums[0] = 2;
	cond0.conditionType[0] = 0;
	cond0.values[0] = (uint8_t*)malloc(4);
	memcpy(cond0.values[0], &val, 4);
	cond0.nextCondition = NULL;

	char* tableNameIndex = "flightTableIndex";
	char* tableNameLinear = "flightTableLinear";

//	createTable(enclave_id, (int*)&status, &flightSchema, tableNameIndex, strlen(tableNameIndex), TYPE_TREE_ORAM, 1010, &structureIdIndex);
//	createTable(enclave_id, (int*)&status, &flightSchema, tableNameLinear, strlen(tableNameLinear), TYPE_LINEAR_SCAN, 1010, &structureIdLinear);
	createTable(enclave_id, (int*)&status, &flightSchema, tableNameIndex, strlen(tableNameIndex), TYPE_TREE_ORAM, 250010, &structureIdIndex);
	createTable(enclave_id, (int*)&status, &flightSchema, tableNameLinear, strlen(tableNameLinear), TYPE_LINEAR_SCAN, 250010, &structureIdLinear);

	std::ifstream file("flight_data_small.csv"); //eclipse doesn't like this line, but it compiles fine

	char line[BLOCK_DATA_SIZE];//make this big just in case
	char data[BLOCK_DATA_SIZE];
	file.getline(line, BLOCK_DATA_SIZE);//burn first line
	row[0] = 'a';
	for(int i = 0; i < 250000; i++){
	//for(int i = 0; i < 1000; i++){
		memset(row, 'a', BLOCK_DATA_SIZE);
		file.getline(line, BLOCK_DATA_SIZE);//get the field

		std::istringstream ss(line);
		for(int j = 0; j < 7; j++){
			if(!ss.getline(data, BLOCK_DATA_SIZE, ',')){
				break;
			}
			//printf("data: %s\n", data);
			int d = 0;
			d = atoi(data);
			//printf("data: %s\n", data);
			//printf("d %d\n", d);
			memcpy(&row[flightSchema.fieldOffsets[j+1]], &d, 4);
		}
		//insert the row into the database - index by last sale price
		int indexval = 0;
		memcpy(&indexval, &row[flightSchema.fieldOffsets[2]], 4);
		insertIndexRowFast(enclave_id, (int*)&status, "flightTableIndex", row, indexval);
		//manually insert into the linear scan structure for speed purposes
		opOneLinearScanBlock(enclave_id, (int*)&status, structureIdLinear, i, (Linear_Scan_Block*)row, 1);
		incrementNumRows(enclave_id, (int*)&status, structureIdLinear);
	}

	//printTable(enclave_id, (int*)&status, "flightTableLinear");
	//now run the query and time it
	printf("created flight tables\n");
	time_t startTime, endTime;
	double elapsedTime;

	startTime = clock();
	selectRows(enclave_id, (int*)&status, "flightTableLinear", 6, cond0, 4, 1, -1, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 1 linear running time small: %.5f\n", elapsedTime);
	printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");

	startTime = clock();
	indexSelect(enclave_id, (int*)&status, "flightTableIndex", 6, cond0, 4, 1, -1, val-1, val, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 1 index running time hash: %.5f\n", elapsedTime);
	printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");

	startTime = clock();
	selectRows(enclave_id, (int*)&status, "flightTableLinear", 6, cond0, -1, -1, 5, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 2 linear running time baseline: %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");

	startTime = clock();
	indexSelect(enclave_id, (int*)&status, "flightTableIndex", 6, cond0, -1, -1, 2, val-1, val, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 2 index running time small: %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
	getNumRows(enclave_id, (int*)&status, 2);
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
	startTime = clock();
	indexSelect(enclave_id, (int*)&status, "flightTableIndex", 6, cond0, -1, -1, 3, val-1, val, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 2 index running time hash: %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
	getNumRows(enclave_id, (int*)&status, 2);
	printf("number of rows selected: %d", (int)status);fflush(stdout);//this is a hack, ReturnTable should be in position 2
    deleteTable(enclave_id, (int*)&status, "ReturnTable");


    deleteTable(enclave_id, (int*)&status, "flightTableLinear");
    deleteTable(enclave_id, (int*)&status, "flightTableIndex");

}

void complaintTables(sgx_enclave_id_t enclave_id, int status){
	//will need to increase block size to 4096 to run this test
	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	int structureIdIndex = -1;
	int structureIdLinear = -1;
	Schema compSchema;
	compSchema.numFields = 14;
	compSchema.fieldOffsets[0] = 0;
	compSchema.fieldSizes[0] = 1;
	compSchema.fieldTypes[0] = CHAR;
	compSchema.fieldOffsets[1] = 1;
	compSchema.fieldSizes[1] = 4;
	compSchema.fieldTypes[1] = INTEGER;
	compSchema.fieldOffsets[2] = 5;
	compSchema.fieldSizes[2] = 255;
	compSchema.fieldTypes[2] = TINYTEXT;
	compSchema.fieldOffsets[3] = 260;
	compSchema.fieldSizes[3] = 255;
	compSchema.fieldTypes[3] = TINYTEXT;
	compSchema.fieldOffsets[4] = 515;
	compSchema.fieldSizes[4] = 255;
	compSchema.fieldTypes[4] = TINYTEXT;
	compSchema.fieldOffsets[5] = 770;
	compSchema.fieldSizes[5] = 4;
	compSchema.fieldTypes[5] = INTEGER;
	compSchema.fieldOffsets[6] = 774;
	compSchema.fieldSizes[6] = 255;
	compSchema.fieldTypes[6] = TINYTEXT;
	compSchema.fieldOffsets[7] = 1029;
	compSchema.fieldSizes[7] = 4;
	compSchema.fieldTypes[7] = INTEGER;
	compSchema.fieldOffsets[8] = 1033;
	compSchema.fieldSizes[8] = 4;
	compSchema.fieldTypes[8] = INTEGER;
	compSchema.fieldOffsets[9] = 1037;
	compSchema.fieldSizes[9] = 255;
	compSchema.fieldTypes[9] = TINYTEXT;
	compSchema.fieldOffsets[10] = 1292;
	compSchema.fieldSizes[10] = 255;
	compSchema.fieldTypes[10] = TINYTEXT;
	compSchema.fieldOffsets[11] = 1547;
	compSchema.fieldSizes[11] = 255;
	compSchema.fieldTypes[11] = TINYTEXT;
	compSchema.fieldOffsets[12] = 1802;
	compSchema.fieldSizes[12] = 255;
	compSchema.fieldTypes[12] = TINYTEXT;
	compSchema.fieldOffsets[13] = 2057;
	compSchema.fieldSizes[13] = 4;
	compSchema.fieldTypes[13] = INTEGER;


printf("here\n");fflush(stdout);
	Condition cond0, cond1, cond2, cond3, cond4, condNone, cond5;
	char* negative = "No";
	char* ccc = "Credit card";
	char* mmm = "Mortgage";
	char* bank = "Bank of America";
	cond0.numClauses = 1;
	cond0.fieldNums[0] = 11;
	cond0.conditionType[0] = 0;
	cond0.values[0] = (uint8_t*)malloc(strlen(negative)+1);
	strcpy((char*)cond0.values[0], negative);
	cond0.nextCondition = &cond1;
	cond1.numClauses = 2;
	cond1.fieldNums[0] = 2;
	cond1.fieldNums[1] = 2;
	cond1.conditionType[0] = 0;
	cond1.conditionType[1] = 0;
	cond1.values[0] = (uint8_t*)malloc(strlen(ccc)+1);
	cond1.values[1] = (uint8_t*)malloc(strlen(mmm)+1);
	strcpy((char*)cond1.values[0], ccc);
	strcpy((char*)cond1.values[1], mmm);
	cond1.nextCondition = NULL;
	cond2.numClauses = 1;
	cond2.fieldNums[0] = 7;
	cond2.conditionType[0] = 1;
	int l = 20130513, h = 20130515;
	cond2.values[0] = (uint8_t*)malloc(4);
	memcpy(cond2.values[0], &l, 4);
	cond2.nextCondition = &cond3;
	cond3.numClauses = 1;
	cond3.fieldNums[0] = 7;
	cond3.conditionType[0] = -1;
	cond3.values[0] = (uint8_t*)malloc(4);
	memcpy(cond3.values[0], &h, 4);
	cond3.nextCondition = NULL;
	cond4.numClauses = 1;
	cond4.fieldNums[0] = 9;
	cond4.conditionType[0] = 0;
	cond4.values[0] = (uint8_t*)malloc(strlen(bank)+1);
	strcpy((char*)cond4.values[0], bank);
	cond4.nextCondition = NULL;

	int rowNumber = 20170817;
	cond5.numClauses = 1;
	cond5.fieldNums[0] = 13;
	cond5.conditionType[0] = 0;
	cond5.values[0] = (uint8_t*)malloc(4);
	memcpy(cond5.values[0], &rowNumber, 4);
	cond5.nextCondition = NULL;

	char* tableNameIndex = "compTableIndex";
	char* tableNameLinear = "compTableLinear";

printf("here\n");fflush(stdout);
	createTable(enclave_id, (int*)&status, &compSchema, tableNameIndex, strlen(tableNameIndex), TYPE_TREE_ORAM, 107000, &structureIdIndex);
	createTable(enclave_id, (int*)&status, &compSchema, tableNameLinear, strlen(tableNameLinear), TYPE_LINEAR_SCAN, 107000, &structureIdLinear);
	//createTable(enclave_id, (int*)&status, &compSchema, tableNameIndex, strlen(tableNameIndex), TYPE_TREE_ORAM, 1010, &structureIdIndex);
printf("here\n");fflush(stdout);
	//createTable(enclave_id, (int*)&status, &compSchema, tableNameLinear, strlen(tableNameLinear), TYPE_LINEAR_SCAN, 1010, &structureIdLinear);

	std::ifstream file("cfpb_consumer_complaints.csv");

	char line[BLOCK_DATA_SIZE];//make this big just in case
	char data[BLOCK_DATA_SIZE];
	file.getline(line, BLOCK_DATA_SIZE);//burn first line
	row[0] = 'a';
printf("here\n");fflush(stdout);
	for(int i = 0; i < 106428; i++){
	//for(int i = 0; i < 1000; i++){
		memset(row, 'a', BLOCK_DATA_SIZE);
		file.getline(line, BLOCK_DATA_SIZE);//get the field

		std::istringstream ss(line);
		for(int j = 0; j < 13; j++){
			if(!ss.getline(data, BLOCK_DATA_SIZE, ',')){
				break;
			}
			//printf("data: %s\n", data);
			if(j == 0 || j== 4 || j == 6 || j == 7 || j == 12){//integer
				int d = 0;
				d = atoi(data);
				//printf("data: %s\n", data);
				//printf("d %d\n", d);
				memcpy(&row[compSchema.fieldOffsets[j+1]], &d, 4);
			}
			else{//tinytext
				strncpy((char*)&row[compSchema.fieldOffsets[j+1]], data, strlen(data)+1);
			}
		}
		//insert the row into the database - index by last sale price
		int indexval = 0;
		memcpy(&indexval, &row[compSchema.fieldOffsets[7]], 4);
		insertIndexRowFast(enclave_id, (int*)&status, "compTableIndex", row, indexval);
		//manually insert into the linear scan structure for speed purposes
		opOneLinearScanBlock(enclave_id, (int*)&status, structureIdLinear, i, (Linear_Scan_Block*)row, 1);
		incrementNumRows(enclave_id, (int*)&status, structureIdLinear);
	}

	//printTable(enclave_id, (int*)&status, "compTableLinear");
	//now run the query and time it
	printf("created complaint tables\n");
	time_t startTime, endTime;
	double elapsedTime;

    l = 20130513;
    h = 20130515;


	startTime = clock();
	indexSelect(enclave_id, (int*)&status, "compTableIndex", -1, cond5, -1, -1, 2, rowNumber-1, rowNumber+1, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("point query index running time small: %.5f\n", elapsedTime);
	startTime = clock();
	indexSelect(enclave_id, (int*)&status, "compTableIndex", -1, cond5, -1, -1, 3, rowNumber-1, rowNumber+1, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("point query index running time hash: %.5f\n", elapsedTime);
	startTime = clock();
	indexSelect(enclave_id, (int*)&status, "compTableIndex", -1, cond5, -1, -1, 1, rowNumber-1, rowNumber+1, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("point query index running time cont: %.5f\n", elapsedTime);

	startTime = clock();
	indexSelect(enclave_id, (int*)&status, "compTableIndex", -1, cond2, -1, -1, 2, l, h, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 2 index running time small: %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
	startTime = clock();
	indexSelect(enclave_id, (int*)&status, "compTableIndex", -1, cond2, -1, -1, 3, l, h, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 2 index running time hash: %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
	startTime = clock();
	indexSelect(enclave_id, (int*)&status, "compTableIndex", -1, cond2, -1, -1, 5, l, h, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 2 index running time baseline: %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");


	startTime = clock();
	deleteRow(enclave_id, (int*)&status, "compTableIndex", l);
	//int deleteRows(char* tableName, Condition c, int startKey, int endKey) {
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("index single deletion running time: %.5f\n", elapsedTime);

	startTime = clock();
	deleteRows(enclave_id, (int*)&status, "compTableIndex", cond4, l, h);
	//int deleteRows(char* tableName, Condition c, int startKey, int endKey) {
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("index deletion running time: %.5f\n", elapsedTime);

	//make row to insert
	uint8_t* rowInsert = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	row[0] = 'a';
	row[7] = 20170101;
	//the rest of the fields don't matter

	startTime = clock();
	insertRow(enclave_id, (int*)&status, "compTableIndex", rowInsert, 20170101);
	//int insertRow(char* tableName, uint8_t* row, int key)
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("index insertion running time: %.5f\n", elapsedTime);


	startTime = clock();
	selectRows(enclave_id, (int*)&status, "compTableLinear", -1, cond2, -1, -1, 2, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 2 linear running time small: %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
	startTime = clock();
	selectRows(enclave_id, (int*)&status, "compTableLinear", -1, cond2, -1, -1, 3, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 2 linear running time hash: %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
	startTime = clock();
	selectRows(enclave_id, (int*)&status, "compTableLinear", -1, cond2, -1, -1, 5, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 2 linear running time baseline: %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");


    cond1.nextCondition = NULL;
    //SELECT count(*) from CFPB where (PRODUCT = "Credit Card" OR Product = "Mortgaga") AND Timely_Response="No" GROUP BY Bank

	startTime = clock();
	selectRows(enclave_id, (int*)&status, "compTableLinear", 1, cond0, 0, 9, -1, 0);
	//sgx_status_t selectRows(sgx_enclave_id_t eid, int* retval, char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice, int intermediate)
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 1 linear running time: %.5f\n", elapsedTime);
	printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
	startTime = clock();
	selectRows(enclave_id, (int*)&status, "compTableLinear", 1, cond0, 0, 9, -1, 2);
	//sgx_status_t selectRows(sgx_enclave_id_t eid, int* retval, char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice, int intermediate)
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 1 linear running time baseline: %.5f\n", elapsedTime);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");

    deleteTable(enclave_id, (int*)&status, "compTableLinear");
}

void nasdaqTables(sgx_enclave_id_t enclave_id, int status){
	//block data size must be at least 2048 here
//create a linear scan table and an index for the flight test data. Index the data by the destination city
	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	int structureIdLinear = -1;
	Schema nasSchema;
	nasSchema.numFields = 11;
	nasSchema.fieldOffsets[0] = 0;
	nasSchema.fieldSizes[0] = 1;
	nasSchema.fieldTypes[0] = CHAR;
	nasSchema.fieldOffsets[1] = 1;
	nasSchema.fieldSizes[1] = 255;
	nasSchema.fieldTypes[1] = TINYTEXT;
	nasSchema.fieldOffsets[2] = 256;
	nasSchema.fieldSizes[2] = 255;
	nasSchema.fieldTypes[2] = TINYTEXT;
	nasSchema.fieldOffsets[3] = 511;
	nasSchema.fieldSizes[3] = 4;
	nasSchema.fieldTypes[3] = INTEGER;
	nasSchema.fieldOffsets[4] = 515;
	nasSchema.fieldSizes[4] = 4;
	nasSchema.fieldTypes[4] = INTEGER;
	nasSchema.fieldOffsets[5] = 519;
	nasSchema.fieldSizes[5] = 255;
	nasSchema.fieldTypes[5] = TINYTEXT;
	nasSchema.fieldOffsets[6] = 774;
	nasSchema.fieldSizes[6] = 255;
	nasSchema.fieldTypes[6] = TINYTEXT;
	nasSchema.fieldOffsets[7] = 1029;
	nasSchema.fieldSizes[7] = 255;
	nasSchema.fieldTypes[7] = TINYTEXT;
	nasSchema.fieldOffsets[8] = 1284;
	nasSchema.fieldSizes[8] = 255;
	nasSchema.fieldTypes[8] = TINYTEXT;
	nasSchema.fieldOffsets[9] = 1539;
	nasSchema.fieldSizes[9] = 255;
	nasSchema.fieldTypes[9] = TINYTEXT;
	nasSchema.fieldOffsets[10] = 1794;
	nasSchema.fieldSizes[10] = 4;
	nasSchema.fieldTypes[10] = INTEGER;

	Condition cond1, cond2, cond3, condNone;
	char* sector = "Technology";
	cond1.numClauses = 1;
	cond1.fieldNums[0] = 7;
	cond1.conditionType[0] = 0;
	cond1.values[0] = (uint8_t*)malloc(strlen(sector)+1);
	strcpy((char*)cond1.values[0], sector);
	cond1.nextCondition = &cond2;
	cond2.numClauses = 1;
	cond2.fieldNums[0] = 3;
	cond2.conditionType[0] = 1;
	int l = 100, h = 200;
	cond2.values[0] = (uint8_t*)malloc(4);
	memcpy(cond2.values[0], &l, 4);
	cond2.nextCondition = &cond3;
	cond3.numClauses = 1;
	cond3.fieldNums[0] = 3;
	cond3.conditionType[0] = -1;
	cond3.values[0] = (uint8_t*)malloc(4);
	memcpy(cond3.values[0], &h, 4);
	cond3.nextCondition = NULL;
	condNone.numClauses = 0;
	condNone.nextCondition = NULL;

	char* tableNameLinear = "nasTableLinear";

	createTable(enclave_id, (int*)&status, &nasSchema, tableNameLinear, strlen(tableNameLinear), TYPE_LINEAR_SCAN, 3300, &structureIdLinear);

	//printf("status %d\n", s);

	std::ifstream file("nasdaq_data.csv"); //eclipse doesn't like this line, but it compiles fine

	char line[BLOCK_DATA_SIZE];//make this big just in case
	char data[BLOCK_DATA_SIZE];
	file.getline(line, BLOCK_DATA_SIZE);//burn first line
	row[0] = 'a';
	for(int i = 0; i < 3209; i++){
		memset(row, 'a', BLOCK_DATA_SIZE);
		file.getline(line, BLOCK_DATA_SIZE);//get the field

		std::istringstream ss(line);
		for(int j = 0; j < 10; j++){
			if(!ss.getline(data, BLOCK_DATA_SIZE, ',')){
				break;
			}
			//printf("data: %s\n", data);
			if(j == 2 || j== 3 || j == 9){//integer
				int d = 0;
				d = atoi(data);
				//printf("data: %s\n", data);
				//printf("d %d\n", d);
				memcpy(&row[nasSchema.fieldOffsets[j+1]], &d, 4);
			}
			else{//tinytext
				strncpy((char*)&row[nasSchema.fieldOffsets[j+1]], data, strlen(data)+1);
			}
		}
		//manually insert into the linear scan structure for speed purposes
		opOneLinearScanBlock(enclave_id, (int*)&status, structureIdLinear, i, (Linear_Scan_Block*)row, 1);
		incrementNumRows(enclave_id, (int*)&status, structureIdLinear);
	}

	//printTable(enclave_id, (int*)&status, "nasTableLinear");
	//now run the query and time it
	printf("created nasdaq tables\n");
	time_t startTime, endTime;
	double elapsedTime;


	startTime = clock();
	selectRows(enclave_id, (int*)&status, "nasTableLinear", 1, cond1, -1, -1, 2, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 1 linear running time small: %.5f\n", elapsedTime);
    deleteTable(enclave_id, (int*)&status, "ReturnTable");

	startTime = clock();
	selectRows(enclave_id, (int*)&status, "nasTableLinear", 1, cond1, -1, -1, 5, 0);
	endTime = clock();
	elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
	printf("query 1 linear running time baseline: %.5f\n", elapsedTime);
    deleteTable(enclave_id, (int*)&status, "ReturnTable");

    deleteTable(enclave_id, (int*)&status, "nasTableLinear");
}

void basicTests(sgx_enclave_id_t enclave_id, int status){

	        Condition condition1, condition2, condition3, noCondition, gapCond1, gapCond2;
	        char a = 'a', b = 'b', c='c';
	        int low = 1, high = 900, lowPlusOne = 2;
	        condition1.numClauses = 2;
	        condition1.fieldNums[0] = 3;
	        condition1.fieldNums[1] = 3;
	        condition1.conditionType[0] = 0;
	        condition1.conditionType[1] = 0;
	        condition1.values[0] = (uint8_t*)&a;
	        condition1.values[1] = (uint8_t*)&b;
	        condition1.nextCondition = &condition2;
	        condition2.numClauses = 1;
	        condition2.fieldNums[0] = 1;
	        condition2.conditionType[0] = 1;
	        condition2.values[0] = (uint8_t*)&low;
	        condition2.nextCondition = &condition3;
	        condition3.numClauses = 1;
	        condition3.fieldNums[0] = 1;
	        condition3.conditionType[0] = -1;
	        condition3.values[0] = (uint8_t*)&high;
	        condition3.nextCondition = NULL;
	        noCondition.numClauses = 0;
	        noCondition.nextCondition = NULL;
	        gapCond1.numClauses = 2;
	        gapCond1.fieldNums[0] = 1;
	        gapCond1.conditionType[0] = -1;
	        gapCond1.values[0] = (uint8_t*)&low;
	        gapCond1.fieldNums[1] = 1;
	        gapCond1.conditionType[1] = 1;
	        gapCond1.values[1] = (uint8_t*)&lowPlusOne;
	        gapCond1.nextCondition = &condition2;

	    	Schema testSchema;
	    	testSchema.numFields = 5;
	    	testSchema.fieldOffsets[0] = 0;
	    	testSchema.fieldOffsets[1] = 1;
	    	testSchema.fieldOffsets[2] = 5;
	    	testSchema.fieldOffsets[3] = 9;
	    	testSchema.fieldOffsets[4] = 10;
	    	testSchema.fieldSizes[0] = 1;
	    	testSchema.fieldSizes[1] = 4;
	    	testSchema.fieldSizes[2] = 4;
	    	testSchema.fieldSizes[3] = 1;
	    	testSchema.fieldSizes[4] = 255;
	    	testSchema.fieldTypes[0] = CHAR;
	    	testSchema.fieldTypes[1] = INTEGER;
	    	testSchema.fieldTypes[2] = INTEGER;
	    	testSchema.fieldTypes[3] = CHAR;
	    	testSchema.fieldTypes[4] = TINYTEXT;
	    	Schema testSchema2;
	    	testSchema2.numFields = 4;
	    	testSchema2.fieldOffsets[0] = 0;
	    	testSchema2.fieldOffsets[1] = 1;
	    	testSchema2.fieldOffsets[2] = 5;
	    	testSchema2.fieldOffsets[3] = 9;
	    	testSchema2.fieldSizes[0] = 1;
	    	testSchema2.fieldSizes[1] = 4;
	    	testSchema2.fieldSizes[2] = 4;
	    	testSchema2.fieldSizes[3] = 1;
	    	testSchema2.fieldTypes[0] = CHAR;
	    	testSchema2.fieldTypes[1] = INTEGER;
	    	testSchema2.fieldTypes[2] = INTEGER;
	    	testSchema2.fieldTypes[3] = CHAR;

    //test to create table and print it
    createTestTable(enclave_id, (int*)&status, "myTestTable", 100);
    //printTable(enclave_id, (int*)&status, "myTestTable");
printf("created\n");
//selectRows(enclave_id, (int*)&status, "testTable", -1, condition1, -1, -1, 1);
//printTable(enclave_id, (int*)&status, "ReturnTable");
//printf("deleting\n");

//deleteTable(enclave_id, (int*)&status, "ReturnTable");
//printf("deleted\n");
/*
selectRows(enclave_id, (int*)&status, "testTable", -1, condition1, -1, -1, 2);
printf("printing\n");

printTable(enclave_id, (int*)&status, "ReturnTable");
printf("deleting\n");

deleteTable(enclave_id, (int*)&status, "ReturnTable");
printf("deleted\n");


selectRows(enclave_id, (int*)&status, "testTable", -1, condition1, -1, -1, 3);
printf("printing");
printTable(enclave_id, (int*)&status, "ReturnTable");
printf("deleting");
deleteTable(enclave_id, (int*)&status, "ReturnTable");
printf("deleted");

selectRows(enclave_id, (int*)&status, "testTable", -1, condition1, -1, -1, 4);
printTable(enclave_id, (int*)&status, "ReturnTable");
deleteTable(enclave_id, (int*)&status, "ReturnTable");
*/

    //test to satisfy conditions on rows
    Schema s;
    getTableSchema(enclave_id, &s, "myTestTable");
    uint8_t* row1 = (uint8_t*)malloc(BLOCK_DATA_SIZE);
    row1[0] = 'a';
    int val = 260;
    memcpy(&row1[1], &val, 4);
    //row1[1] = 260;
    int val2 = 313;
    memcpy(&row1[5], &val2, 4);
    row1[9] = 'b';
    int output = 0;
    rowMatchesCondition(enclave_id, &output, condition1, row1, s);
    printf("row1 matches condition: %d", output);

    //test to insert, update, delete

    insertRow(enclave_id, (int*)&status, "myTestTable", row1, -1);
    insertRow(enclave_id, (int*)&status, "myTestTable", row1, -1);
    printTable(enclave_id, (int*)&status, "myTestTable");
    updateRows(enclave_id, (int*)&status, "myTestTable", condition2, 2, &row1[5], -1, -1);
    printTable(enclave_id, (int*)&status, "myTestTable");
    deleteRows(enclave_id, (int*)&status, "myTestTable", condition2, -1, -1);
    printTable(enclave_id, (int*)&status, "myTestTable");


    //test select aggregate without group
//int selectRows(char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice)
    selectRows(enclave_id, (int*)&status, "myTestTable", 1, condition2, 0, -1, -1, 0);
    printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");


    //test select continuous:

    selectRows(enclave_id, (int*)&status, "myTestTable", -1, condition2, -1, -1, -1, 0);
    printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");



    //test select almost all: (depending on how much extra space is left in the table data structure)
    createTestTable(enclave_id, (int*)&status, "myTestTable2", 110);
    insertRow(enclave_id, (int*)&status, "myTestTable2", row1, -1);
    insertRow(enclave_id, (int*)&status, "myTestTable2", row1, -1);
    printTable(enclave_id, (int*)&status, "myTestTable2");
    selectRows(enclave_id, (int*)&status, "myTestTable2", -1, condition2, -1, -1, -1, 0);
    printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");


    //test select small:

    createTestTable(enclave_id, (int*)&status, "myTestTable2", 50);
    insertRow(enclave_id, (int*)&status, "myTestTable2", row1, -1);
    insertRow(enclave_id, (int*)&status, "myTestTable2", row1, -1);
    printTable(enclave_id, (int*)&status, "myTestTable2");
    selectRows(enclave_id, (int*)&status, "myTestTable2", -1, condition2, -1, -1, -1, 0);
    printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");


    //test group by
    //int selectRows(char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice)
    selectRows(enclave_id, (int*)&status, "myTestTable", 1, condition1, 0, 3, -1, 0);
    printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");


    //test select hash

    createTestTable(enclave_id, (int*)&status, "myTestTable2", 50);
    insertRow(enclave_id, (int*)&status, "myTestTable2", row1, -1);
    selectRows(enclave_id, (int*)&status, "myTestTable2", -1, condition2, -1, -1, -1, 0);
    printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");


    //test join

    createTestTable(enclave_id, (int*)&status, "join1", 50);
    createTestTable(enclave_id, (int*)&status, "join2", 50);
    deleteRows(enclave_id, (int*)&status, "join2", condition1, -1, -1);
    printTable(enclave_id, (int*)&status, "join2");
    joinTables(enclave_id, (int*)&status, "join1", "join2", 1, 1, -1, -1);
    printTable(enclave_id, (int*)&status, "JoinReturn");
    printTable(enclave_id, (int*)&status, "join2");
    selectRows(enclave_id, (int*)&status, "JoinReturn", 1, condition3, 0, 3, -1, 0);
    printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "JoinReturn");
    deleteTable(enclave_id, (int*)&status, "join1");
    deleteTable(enclave_id, (int*)&status, "join2");


    //Start Index tests
    printf("start index tests\n");

    createTestTableIndex(enclave_id, (int*)&status, "myTestIndex", 15);
    //printTable(enclave_id, (int*)&status, "myTestIndex");

    //indexSelect(enclave_id, (int*)&status, "myTestIndex", 1, condition1, 0, 3, -1, 2, 250);
    indexSelect(enclave_id, (int*)&status, "myTestIndex", -1, condition1, -1, -1, -1, 2, 250, 0);
    printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");

    //insertRow(enclave_id, (int*)&status, "myTestIndex", row1, 260);
    //insertRow(enclave_id, (int*)&status, "myTestIndex", row1, 260);
    //updateRows(enclave_id, (int*)&status, "myTestIndex", condition2, 2, &row1[5], 2, 7);
    deleteRows(enclave_id, (int*)&status, "myTestIndex", condition1, 2, 20);
    deleteRows(enclave_id, (int*)&status, "myTestIndex", condition1, 2, 20);
    deleteRows(enclave_id, (int*)&status, "myTestIndex", condition1, 2, 20);
    deleteRows(enclave_id, (int*)&status, "myTestIndex", condition1, 2, 20);
    deleteRows(enclave_id, (int*)&status, "myTestIndex", condition1, 2, 20);
    deleteRows(enclave_id, (int*)&status, "myTestIndex", condition1, 2, 20);
    deleteRows(enclave_id, (int*)&status, "myTestIndex", condition1, 2, 20);
    deleteRows(enclave_id, (int*)&status, "myTestIndex", condition1, 2, 20);
    deleteRows(enclave_id, (int*)&status, "myTestIndex", condition1, 2, 20);
    deleteRows(enclave_id, (int*)&status, "myTestIndex", condition1, 2, 20);
    indexSelect(enclave_id, (int*)&status, "myTestIndex", -1, noCondition, -1, -1, -1, 2, 270, 0);
    printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
    //test join

    createTestTableIndex(enclave_id, (int*)&status, "jointestTable", 50);
    createTestTableIndex(enclave_id, (int*)&status, "jIndex", 50);
    deleteRows(enclave_id, (int*)&status, "jIndex", condition1, 2, 37);
    deleteRows(enclave_id, (int*)&status, "jIndex", condition1, 2, 37);
    deleteRows(enclave_id, (int*)&status, "jIndex", condition1, 2, 37);
    deleteRows(enclave_id, (int*)&status, "jIndex", condition1, 2, 37);

    indexSelect(enclave_id, (int*)&status, "jointestTable", -1, noCondition, -1, -1, -1, 0, 100, 0);
    printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
    indexSelect(enclave_id, (int*)&status, "jIndex", -1, noCondition, -1, -1, -1, -1, 100, 0);
    printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");

    joinTables(enclave_id, (int*)&status, "jointestTable", "jIndex", 1, 1, 2, 21);
    printTable(enclave_id, (int*)&status, "JoinReturn");
    selectRows(enclave_id, (int*)&status, "JoinReturn", 1, noCondition, 0, 3, -1, 0);
    printTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "ReturnTable");
    deleteTable(enclave_id, (int*)&status, "JoinReturn");

}

void workloadTests(sgx_enclave_id_t enclave_id, int status){

    Condition condition1, condition2, noCondition, neverCondition;
    char a = 'a', b = 'b', c='c';
    int low = 1, high = 100;

    condition1.numClauses = 1;
    condition1.fieldNums[0] = 1;
    condition1.conditionType[0] = 1;
    condition1.values[0] = (uint8_t*)&low;
    condition1.nextCondition = &condition2;
    condition2.numClauses = 1;
    condition2.fieldNums[0] = 1;
    condition2.conditionType[0] = -1;
    condition2.values[0] = (uint8_t*)&high;
    condition2.nextCondition = NULL;
    noCondition.numClauses = 0;
    noCondition.nextCondition = NULL;

    neverCondition.numClauses = 1;
    neverCondition.fieldNums[0] = 1;
    neverCondition.conditionType[0] = -1;
    neverCondition.values[0] = (uint8_t*)&low;
    neverCondition.nextCondition = NULL;

	Schema testSchema;
	testSchema.numFields = 5;
	testSchema.fieldOffsets[0] = 0;
	testSchema.fieldOffsets[1] = 1;
	testSchema.fieldOffsets[2] = 5;
	testSchema.fieldOffsets[3] = 9;
	testSchema.fieldOffsets[4] = 10;
	testSchema.fieldSizes[0] = 1;
	testSchema.fieldSizes[1] = 4;
	testSchema.fieldSizes[2] = 4;
	testSchema.fieldSizes[3] = 1;
	testSchema.fieldSizes[4] = 255;
	testSchema.fieldTypes[0] = CHAR;
	testSchema.fieldTypes[1] = INTEGER;
	testSchema.fieldTypes[2] = INTEGER;
	testSchema.fieldTypes[3] = CHAR;
	testSchema.fieldTypes[4] = TINYTEXT;

	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	const char* text = "You would measure time the measureless and the immeasurable.";
	int testSize = 100000;
	row[0] = 'a';
	memcpy(&row[1], &testSize, 4);
	int temp = testSize/100;
	memcpy(&row[5], &temp, 4);
	if((testSize)%2 == 0) row[9] = 'a';
	else if((testSize)%3 == 0) row[9] = 'b';
	else row[9]= 'c';
	memcpy(&row[10], text, strlen(text)+1);

	time_t startOp, endOp;
	double elapsedTime, tempTime;
	int i = 0;

	//workload 1
	low = 1; high = 100;
    createTestTable(enclave_id, (int*)&status, "Linear", 100000);
    createTestTableIndex(enclave_id, (int*)&status, "Index", 100000);
    i = 0;
    startOp = clock();
    while(i<90){
    	insertLinRowFast(enclave_id, (int*)&status, "Linear", row);
 	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 1 linear insertion time: %.5f\n", elapsedTime);
    high = 3;

    elapsedTime = 0;
    while(i<95){
        startOp = clock();
    	selectRows(enclave_id, (int*)&status, "Linear", -1, condition1, -1, -1, -1, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);

    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }
    printf("workload 1 linear small read time: %.5f\n", elapsedTime);
    high=5000;

    elapsedTime = 0;
    while(i<100){
        startOp = clock();
    	selectRows(enclave_id, (int*)&status, "Linear", -1, condition1, -1, -1, -1, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }

    printf("workload 1 linear large read time: %.5f\n", elapsedTime);
    //switch to index
    i = 0;
    startOp = clock();
    while(i<90){
    	insertRow(enclave_id, (int*)&status, "Index", row, 100000);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 1 index insertion time: %.5f\n", elapsedTime);
    high = 3;

    elapsedTime = 0;
    while(i<95){
        startOp = clock();
    	indexSelect(enclave_id, (int*)&status, "Index", -1, condition1, -1, -1, -1, low, high,0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }

    printf("workload 1 index small read time: %.5f\n", elapsedTime);
    high=5000;
    elapsedTime = 0;
    
    while(i<100){
        startOp = clock();
    	indexSelect(enclave_id, (int*)&status, "Index", -1, condition1, -1, -1, -1, low, high,0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }
    printf("workload 1 index large read time: %.5f\n", elapsedTime);

    deleteTable(enclave_id, (int*)&status, "Linear");
    //deleteTable(enclave_id, (int*)&status, "Index"); we'll reuse this

    //
    //
	//workload 2
	low = 1; high = 100;
    createTestTable(enclave_id, (int*)&status, "Linear", 100000);
    //createTestTableIndex(enclave_id, (int*)&status, "Index", 100000);
    i = 0;
    high = 51;
    elapsedTime = 0;
    while(i<90){
        startOp = clock();
    	selectRows(enclave_id, (int*)&status, "Linear", -1, condition1, -1, -1, -1, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }

    printf("workload 2 linear select time: %.5f\n", elapsedTime);
    startOp = clock();
    while(i<99){
    	insertLinRowFast(enclave_id, (int*)&status, "Linear", row);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 2 linear insertion time: %.5f\n", elapsedTime);

    low=5999; high = 6002;
    startOp = clock();
    while(i<100){
    	deleteRows(enclave_id, (int*)&status, "Linear", condition1, low,high);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 2 linear deletion time: %.5f\n", elapsedTime);
    //switch to index
    i = 0;
    low = 1;
    high = 51;
    elapsedTime = 0;
    while(i<90){
        startOp = clock();
    	indexSelect(enclave_id, (int*)&status, "Index", -1, condition1, -1, -1, -1, low, high, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }
    printf("workload 2 index select time: %.5f\n", elapsedTime);
    startOp = clock();
    while(i<99){
    	insertRow(enclave_id, (int*)&status, "Index", row, 100000);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 2 index insertion time: %.5f\n", elapsedTime);
    low=5999; high = 6002;
    startOp = clock();
    while(i<100){
    	deleteRows(enclave_id, (int*)&status, "Index", condition1, low, high);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 2 index deletion time: %.5f\n", elapsedTime);

    deleteTable(enclave_id, (int*)&status, "Linear");
    //deleteTable(enclave_id, (int*)&status, "Index");


    //
	//workload 3
	low = 1; high = 100;
    createTestTable(enclave_id, (int*)&status, "Linear", 100000);
    //createTestTableIndex(enclave_id, (int*)&status, "Index", 100000);
    i = 0;
    
    high = 3;
    elapsedTime = 0;
    while(i<50){
        startOp = clock();
    	selectRows(enclave_id, (int*)&status, "Linear", -1, condition1, -1, -1, -1, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }
    
    printf("workload 3 linear small select time: %.5f\n", elapsedTime);
    high = 5000;
    elapsedTime = 0;
    while(i<100){
        startOp = clock();
    	selectRows(enclave_id, (int*)&status, "Linear", -1, condition1, -1, -1, -1, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }
    
    printf("workload 3 linear large select time: %.5f\n", elapsedTime);

    //switch to index
    i = 0;
    high = 3;
    elapsedTime = 0;
    while(i<50){
        startOp = clock();
    	indexSelect(enclave_id, (int*)&status, "Index", -1, condition1, -1, -1, -1, low, high, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }
    printf("workload 3 index small select time: %.5f\n", elapsedTime);
    high = 5000;
    elapsedTime = 0;
    while(i<100){
        startOp = clock();
    	indexSelect(enclave_id, (int*)&status, "Index", -1, condition1, -1, -1, -1, low, high, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }
    printf("workload 3 index large select time: %.5f\n", elapsedTime);

    deleteTable(enclave_id, (int*)&status, "Linear");
    //deleteTable(enclave_id, (int*)&status, "Index");


	//workload 4
	low = 1; high = 100;
    createTestTable(enclave_id, (int*)&status, "Linear", 100000);
    //createTestTableIndex(enclave_id, (int*)&status, "Index", 100000);
    i = 0;
    high = 3;
    elapsedTime = 0;
    while(i<45){
        startOp = clock();
    	selectRows(enclave_id, (int*)&status, "Linear", -1, condition1, -1, -1, -1, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }
    printf("workload 4 linear small select time: %.5f\n", elapsedTime);
    high = 5000;
    elapsedTime = 0;
    while(i<90){
        startOp = clock();
    	selectRows(enclave_id, (int*)&status, "Linear", -1, condition1, -1, -1, -1, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }
    printf("workload 4 linear large select time: %.5f\n", elapsedTime);
    startOp = clock();
    while(i<95){
    	insertLinRowFast(enclave_id, (int*)&status, "Linear", row);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 4 linear insertion time: %.5f\n", elapsedTime);

    low=6000; high = 6003;
    startOp = clock();
    while(i<100){
    	deleteRows(enclave_id, (int*)&status, "Linear", noCondition, low, high);
    	low = 6001; high = 6004;
    	deleteRows(enclave_id, (int*)&status, "Linear", noCondition, low, high);
    	low = 6002; high = 6005;
    	deleteRows(enclave_id, (int*)&status, "Linear", noCondition, low, high);
    	low = 6003; high = 6006;
    	deleteRows(enclave_id, (int*)&status, "Linear", noCondition, low, high);
    	low = 6004; high = 6007;
    	deleteRows(enclave_id, (int*)&status, "Linear", noCondition, low, high);
    	low = 6005; high = 6008;
    	i+=5;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 4 linear deletion time: %.5f\n", elapsedTime);

    //switch to index
    i = 0;
    low = 1;
    high = 3;
    elapsedTime = 0;
    while(i<45){
        startOp = clock();
    	indexSelect(enclave_id, (int*)&status, "Index", -1, condition1, -1, -1, -1, low, high, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }
    printf("workload 4 index small select time: %.5f\n", elapsedTime);
    high = 5000;
    elapsedTime = 0;
    while(i<90){
        startOp = clock();
    	indexSelect(enclave_id, (int*)&status, "Index", -1, condition1, -1, -1, -1, low, high, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }
    printf("workload 4 index large select time: %.5f\n", elapsedTime);
    startOp = clock();
    while(i<95){
    	insertRow(enclave_id, (int*)&status, "Index", row, 100000);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 4 index insertion time: %.5f\n", elapsedTime);

    low=6000; high = 6003;
    startOp = clock();
    while(i<100){
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 6001; high = 6004;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 6002; high = 6005;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 6003; high = 6006;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 6004; high = 6007;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 6005; high = 6008;
    	i+=5;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 4 index deletion time: %.5f\n", elapsedTime);
    deleteTable(enclave_id, (int*)&status, "Linear");
    //deleteTable(enclave_id, (int*)&status, "Index");


	//workload 5
	low = 1; high = 100;
    createTestTable(enclave_id, (int*)&status, "Linear", 100000);
    //createTestTableIndex(enclave_id, (int*)&status, "Index", 100000);
    i = 0;
    startOp = clock();
    high = 5000;
    elapsedTime = 0;
    while(i<90){
        startOp = clock();
    	selectRows(enclave_id, (int*)&status, "Linear", -1, condition1, -1, -1, -1, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }
    printf("workload 5 linear large select time: %.5f\n", elapsedTime);
    startOp = clock();
    while(i<95){
    	insertLinRowFast(enclave_id, (int*)&status, "Linear", row);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 5 linear insertion time: %.5f\n", elapsedTime);

    low=6006; high = 6009;
    startOp = clock();
    while(i<100){
    	deleteRows(enclave_id, (int*)&status, "Linear", noCondition, low, high);
    	low = 6007; high = 6010;
    	deleteRows(enclave_id, (int*)&status, "Linear", noCondition, low, high);
    	low = 6008; high = 6011;
    	deleteRows(enclave_id, (int*)&status, "Linear", noCondition, low, high);
    	low = 6009; high = 6012;
    	deleteRows(enclave_id, (int*)&status, "Linear", noCondition, low, high);
    	low = 6010; high = 6013;
    	deleteRows(enclave_id, (int*)&status, "Linear", noCondition, low, high);
    	i+=5;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 5 linear deletion time: %.5f\n", elapsedTime);

    //switch to index
    i = 0;
    low = 1;
    high = 5000;
    elapsedTime = 0;
    while(i<90){
        startOp = clock();
    	indexSelect(enclave_id, (int*)&status, "Index", -1, condition1, -1, -1, -1, low, high, 0);
        endOp = clock();
        elapsedTime += (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    	i++;
    }
    printf("workload 5 index large select time: %.5f\n", elapsedTime);
    startOp = clock();
    while(i<95){
    	insertRow(enclave_id, (int*)&status, "Index", row, 100000);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 5 index insertion time: %.5f\n", elapsedTime);

    low=6006; high = 6009;
    startOp = clock();
    while(i<100){
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 6007; high = 6010;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 6008; high = 6011;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 6009; high = 6012;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 6010; high = 6013;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	i+=5;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("workload 5 index deletion time: %.5f\n", elapsedTime);
    deleteTable(enclave_id, (int*)&status, "Linear");
    //deleteTable(enclave_id, (int*)&status, "Index");

    free(row);
}

void insdelScaling(sgx_enclave_id_t enclave_id, int status){

    Condition condition1, condition2, noCondition, neverCondition;
    char a = 'a', b = 'b', c='c';
    int low = 1, high = 100;

    condition1.numClauses = 1;
    condition1.fieldNums[0] = 1;
    condition1.conditionType[0] = 1;
    condition1.values[0] = (uint8_t*)&low;
    condition1.nextCondition = &condition2;
    condition2.numClauses = 1;
    condition2.fieldNums[0] = 1;
    condition2.conditionType[0] = -1;
    condition2.values[0] = (uint8_t*)&high;
    condition2.nextCondition = NULL;
    noCondition.numClauses = 0;
    noCondition.nextCondition = NULL;

    neverCondition.numClauses = 1;
    neverCondition.fieldNums[0] = 1;
    neverCondition.conditionType[0] = -1;
    neverCondition.values[0] = (uint8_t*)&low;
    neverCondition.nextCondition = NULL;

	Schema testSchema;
	testSchema.numFields = 5;
	testSchema.fieldOffsets[0] = 0;
	testSchema.fieldOffsets[1] = 1;
	testSchema.fieldOffsets[2] = 5;
	testSchema.fieldOffsets[3] = 9;
	testSchema.fieldOffsets[4] = 10;
	testSchema.fieldSizes[0] = 1;
	testSchema.fieldSizes[1] = 4;
	testSchema.fieldSizes[2] = 4;
	testSchema.fieldSizes[3] = 1;
	testSchema.fieldSizes[4] = 255;
	testSchema.fieldTypes[0] = CHAR;
	testSchema.fieldTypes[1] = INTEGER;
	testSchema.fieldTypes[2] = INTEGER;
	testSchema.fieldTypes[3] = CHAR;
	testSchema.fieldTypes[4] = TINYTEXT;

	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	const char* text = "You would measure time the measureless and the immeasurable.";
	int testSize = 100000;
	row[0] = 'a';
	memcpy(&row[1], &testSize, 4);
	int temp = testSize/100;
	memcpy(&row[5], &temp, 4);
	if((testSize)%2 == 0) row[9] = 'a';
	else if((testSize)%3 == 0) row[9] = 'b';
	else row[9]= 'c';
	memcpy(&row[10], text, strlen(text)+1);

	time_t startOp, endOp;
	double elapsedTime;
	int i = 0;

    createTestTableIndex(enclave_id, (int*)&status, "Index", 100);
    //switch to index
    low = 1;
    high = 3;
    startOp = clock();
    	indexSelect(enclave_id, (int*)&status, "Index", -1, condition1, -1, -1, -1, low, high, 0);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("100 row index point select time: %.5f\n", elapsedTime);
    i = 0;
    startOp = clock();
    while(i<5){
    	insertRow(enclave_id, (int*)&status, "Index", row, 100000);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    elapsedTime /=5;
    printf("100 row index insertion time: %.5f\n", elapsedTime);
    low=10; high = 12;
    startOp = clock();
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 11; high = 13;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 12; high = 14;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 13; high = 15;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 14; high = 16;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    elapsedTime /=5;
    printf("100 row index deletion time: %.5f\n", elapsedTime);
    deleteTable(enclave_id, (int*)&status, "Index");

    createTestTableIndex(enclave_id, (int*)&status, "Index", 1000);
    //switch to index
    low = 1;
    high = 3;
    startOp = clock();
    	indexSelect(enclave_id, (int*)&status, "Index", -1, condition1, -1, -1, -1, low, high, 0);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("1000 row index point select time: %.5f\n", elapsedTime);
    i = 0;
    startOp = clock();
    while(i<5){
    	insertRow(enclave_id, (int*)&status, "Index", row, 100000);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    elapsedTime /=5;
    printf("1000 row index insertion time: %.5f\n", elapsedTime);
    low=10; high = 12;
    startOp = clock();
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 11; high = 13;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 12; high = 14;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 13; high = 15;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 14; high = 16;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    elapsedTime /=5;
    printf("1000 row index deletion time: %.5f\n", elapsedTime);
    deleteTable(enclave_id, (int*)&status, "Index");

    createTestTableIndex(enclave_id, (int*)&status, "Index", 10000);
    //switch to index
    low = 1;
    high = 3;
    startOp = clock();
    	indexSelect(enclave_id, (int*)&status, "Index", -1, condition1, -1, -1, -1, low, high, 0);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("10000 row index point select time: %.5f\n", elapsedTime);
    i = 0;
    startOp = clock();
    while(i<5){
    	insertRow(enclave_id, (int*)&status, "Index", row, 100000);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    elapsedTime /=5;
    printf("10000 row index insertion time: %.5f\n", elapsedTime);
    low=10; high = 12;
    startOp = clock();
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 11; high = 13;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 12; high = 14;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 13; high = 15;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 14; high = 16;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    elapsedTime /=5;
    printf("10000 row index deletion time: %.5f\n", elapsedTime);
    deleteTable(enclave_id, (int*)&status, "Index");

    createTestTableIndex(enclave_id, (int*)&status, "Index", 100000);
    //switch to index
    low = 1;
    high = 3;
    startOp = clock();
    	indexSelect(enclave_id, (int*)&status, "Index", -1, condition1, -1, -1, -1, low, high, 0);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("100000 row index point select time: %.5f\n", elapsedTime);
    i = 0;
    startOp = clock();
    while(i<5){
    	insertRow(enclave_id, (int*)&status, "Index", row, 100000);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    elapsedTime /=5;
    printf("100000 row index insertion time: %.5f\n", elapsedTime);
    low=10; high = 12;
    startOp = clock();
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 11; high = 13;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 12; high = 14;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 13; high = 15;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 14; high = 16;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    elapsedTime /=5;
    printf("100000 row index deletion time: %.5f\n", elapsedTime);
    deleteTable(enclave_id, (int*)&status, "Index");

    createTestTableIndex(enclave_id, (int*)&status, "Index", 1000000);
    //switch to index
    low = 1;
    high = 3;
    startOp = clock();
    	indexSelect(enclave_id, (int*)&status, "Index", -1, condition1, -1, -1, -1, low, high, 0);
    	deleteTable(enclave_id, (int*)&status, "ReturnTable");
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    printf("1000000 row index point select time: %.5f\n", elapsedTime);
    i = 0;
    startOp = clock();
    while(i<5){
    	insertRow(enclave_id, (int*)&status, "Index", row, 100000);
    	i++;
    }
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    elapsedTime /=5;
    printf("1000000 row index insertion time: %.5f\n", elapsedTime);
    low=10; high = 12;
    startOp = clock();
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 11; high = 13;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 12; high = 14;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 13; high = 15;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    	low = 14; high = 16;
    	deleteRows(enclave_id, (int*)&status, "Index", noCondition, low, high);
    endOp = clock();
    elapsedTime = (double)(endOp - startOp)/(CLOCKS_PER_SEC);
    elapsedTime /=5;
    printf("1000000 row index deletion time: %.5f\n", elapsedTime);
    deleteTable(enclave_id, (int*)&status, "Index");

    free(row);
}


void joinTests(sgx_enclave_id_t enclave_id, int status){
	//comparing our original join and sort merge join for linear tables
	//using same schema as used for synthetic data in FabTests	

	int testSizes[] = {5000, 10000, 25000};
	int numTests = 3;
    
    //for testing
	//int testSizes[] = {5000};
	//int numTests = 1;
   
	//confusingly, thi sis the first table
	int table2Sizes[] = {1000,5000,10000};
	int num2Tests = 3;

	for(int k = 0; k < num2Tests; k++){
	
	

	int table2Size = table2Sizes[k];
    createTestTable(enclave_id, (int*)&status, "jTable", table2Size);//decide what to do with the size of this one
    //createTestTableIndex(enclave_id, (int*)&status, "jTableIndex", 10000);//decide what to do with the size of this one
    //deleteRows(enclave_id, (int*)&status, "jTable", condition1, -1, -1);

    printf("created tables\n");
	for(int i = 0; i < numTests; i++){
		int testSize = testSizes[i];
        	createTestTable(enclave_id, (int*)&status, "testTable", testSize);
        	//createTestTableIndex(enclave_id, (int*)&status, "testTableIndex", testSize);
		printf("\n|Test Sizes %d %d:\n", table2Size, testSize);

        	double join1Times[6] = {0};
        	double join2Times[6] = {0};
        	double join3Times[6] = {0};
        	double join4Times[6] = {0};
        	time_t startTime, endTime;
        	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
        	const char* text = "You would measure time the measureless and the immeasurable.";

    		for(int j = 0; j < 5; j++){ //want to average 5 trials

		//join 1
               	startTime = clock();
               	joinTables(enclave_id, (int*)&status, "jTable", "testTable", 1, 1, -1, -1);
               	endTime = clock();
               	join1Times[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
		//printTableCheating(enclave_id, (int*)&status, "JoinReturn");
               	deleteTable(enclave_id, (int*)&status, "JoinReturn");

                //join 2
                startTime = clock();
                joinTables(enclave_id, (int*)&status, "jTable", "testTable", 1, 1, -1, -248);
                endTime = clock();
                join2Times[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
		//printTableCheating(enclave_id, (int*)&status, "JoinReturn");
                deleteTable(enclave_id, (int*)&status, "JoinReturn");
	
		//join 3
                startTime = clock();
                joinTables(enclave_id, (int*)&status, "jTable", "testTable", 1, 1, -249, -248);
                endTime = clock();
                join3Times[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
		//printTableCheating(enclave_id, (int*)&status, "JoinReturn");
                deleteTable(enclave_id, (int*)&status, "JoinReturn");
		/*
                //join 4
                startTime = clock();
                joinTables(enclave_id, (int*)&status, "jTableIndex", "testTableIndex", 1, 1, 1, testSize);
                endTime = clock();
                join4Times[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
                deleteTable(enclave_id, (int*)&status, "JoinReturn");
		*/

    		}
    		free(row);
    		for(int j = 0; j < 5; j++){
            		join1Times[5] += join1Times[j];
            		join2Times[5] += join2Times[j];
            		join3Times[5] += join3Times[j];
            		join4Times[5] += join4Times[j];
    		}
        	join1Times[5] /= 5;
        	join2Times[5] /= 5;
        	join3Times[5] /= 5;
        	join4Times[5] /= 5;
    		printf("\njoin1Times | %.5f %.5f %.5f %.5f %.5f : %.5f\n", join1Times[0], join1Times[1], join1Times[2], join1Times[3], join1Times[4], join1Times[5]);
    		printf("join2Times | %.5f %.5f %.5f %.5f %.5f : %.5f\n", join2Times[0], join2Times[1], join2Times[2], join2Times[3], join2Times[4], join2Times[5]);
    		printf("join3Times | %.5f %.5f %.5f %.5f %.5f : %.5f\n", join3Times[0], join3Times[1], join3Times[2], join3Times[3], join3Times[4], join3Times[5]);
    		printf("(not in use) join4Times | %.5f %.5f %.5f %.5f %.5f : %.5f\n", join4Times[0], join4Times[1], join4Times[2], join4Times[3], join4Times[4], join4Times[5]);
            
            deleteTable(enclave_id, (int*)&status, "testTable");
            //deleteTable(enclave_id, (int*)&status, "testTableIndex");
	}
    deleteTable(enclave_id, (int*)&status, "jTable");
    //deleteTable(enclave_id, (int*)&status, "jTableIndex");
	}
}


void fabTests(sgx_enclave_id_t enclave_id, int status){
    //Tests for database functionalities here

    Condition condition1, condition2, condition3, noCondition, gapCond1, gapCond2;
    char a = 'a', b = 'b', c='c';
    int low = 1, high = 900, lowPlusOne = 2;
    condition1.numClauses = 2;
    condition1.fieldNums[0] = 3;
    condition1.fieldNums[1] = 3;
    condition1.conditionType[0] = 0;
    condition1.conditionType[1] = 0;
    condition1.values[0] = (uint8_t*)&a;
    condition1.values[1] = (uint8_t*)&b;
    condition1.nextCondition = &condition2;
    condition2.numClauses = 1;
    condition2.fieldNums[0] = 1;
    condition2.conditionType[0] = 1;
    condition2.values[0] = (uint8_t*)&low;
    condition2.nextCondition = &condition3;
    condition3.numClauses = 1;
    condition3.fieldNums[0] = 1;
    condition3.conditionType[0] = -1;
    condition3.values[0] = (uint8_t*)&high;
    condition3.nextCondition = NULL;
    noCondition.numClauses = 0;
    noCondition.nextCondition = NULL;
    gapCond1.numClauses = 2;
    gapCond1.fieldNums[0] = 1;
    gapCond1.conditionType[0] = -1;
    gapCond1.values[0] = (uint8_t*)&low;
    gapCond1.fieldNums[1] = 1;
    gapCond1.conditionType[1] = 1;
    gapCond1.values[1] = (uint8_t*)&lowPlusOne;
    gapCond1.nextCondition = &condition2;

	Schema testSchema;
	testSchema.numFields = 5;
	testSchema.fieldOffsets[0] = 0;
	testSchema.fieldOffsets[1] = 1;
	testSchema.fieldOffsets[2] = 5;
	testSchema.fieldOffsets[3] = 9;
	testSchema.fieldOffsets[4] = 10;
	testSchema.fieldSizes[0] = 1;
	testSchema.fieldSizes[1] = 4;
	testSchema.fieldSizes[2] = 4;
	testSchema.fieldSizes[3] = 1;
	testSchema.fieldSizes[4] = 255;
	testSchema.fieldTypes[0] = CHAR;
	testSchema.fieldTypes[1] = INTEGER;
	testSchema.fieldTypes[2] = INTEGER;
	testSchema.fieldTypes[3] = CHAR;
	testSchema.fieldTypes[4] = TINYTEXT;
	Schema testSchema2;
	testSchema2.numFields = 4;
	testSchema2.fieldOffsets[0] = 0;
	testSchema2.fieldOffsets[1] = 1;
	testSchema2.fieldOffsets[2] = 5;
	testSchema2.fieldOffsets[3] = 9;
	testSchema2.fieldSizes[0] = 1;
	testSchema2.fieldSizes[1] = 4;
	testSchema2.fieldSizes[2] = 4;
	testSchema2.fieldSizes[3] = 1;
	testSchema2.fieldTypes[0] = CHAR;
	testSchema2.fieldTypes[1] = INTEGER;
	testSchema2.fieldTypes[2] = INTEGER;
	testSchema2.fieldTypes[3] = CHAR;


	//time to test performance of everything

	int testSizes[] = {100000};
	int numTests = 1;
	//int testSizes[] = {500};//for testing
	//int numTests = 1;
    createTestTableIndex(enclave_id, (int*)&status, "jIndex", high);
    deleteRows(enclave_id, (int*)&status, "jIndex", condition1, low, high);
    createTestTable(enclave_id, (int*)&status, "jTable", high);
    deleteRows(enclave_id, (int*)&status, "jTable", condition1, -1, -1);
	char tableName[20];
	int testSize = testSizes[0];
	sprintf(tableName, "testTable%d", testSize);
    createTestTable(enclave_id, (int*)&status, "testTable", testSize);
    createTestTableIndex(enclave_id, (int*)&status, tableName, testSize);
    //loadIndexTable(enclave_id, (int*)&status, testSize);
    printf("created tables\n");
	for(int i = 0; i < numTests; i++){
		int testSize = testSizes[i];
		printf("\n\n|Test Size %d:\n", testSize);

		//first we'll do the read-only tests
		int numInnerTests = 3;//how many points do we want along the line
		for(int testRound = 0; testRound <= numInnerTests; testRound++){
			//if(testRound > numInnerTests/6){
			//	testRound = numInnerTests;
			//}
		//if(i == 0){
		//	testRound = numInnerTests;
		//}
			//testRound = numInnerTests; //temp for testing
			printf("test round %d: ", testRound);

			if(testRound < numInnerTests){
				//printf("querying %d%% of table\n", (int)((double)1/numInnerTests*100*(testRound+1)));
				printf("%d rows", (testRound+1)*500);
				//printf("query %d rows of db\n", testSize - (testRound*5000));
			}
			else{
				printf("doing insert, update, delete queries and miscellaneous stuff\n");
			}
        	double insertTimes[6] = {0};//average will be stored in last entry
        	double updateTimes[6] = {0};
        	double deleteTimes[6] = {0};
        	double aggregateTimes[6] = {0};
        	double groupByTimes[6] = {0};
        	double selectTimes[6] = {0};
        	double contTimes[6] = {0};
        	double smallTimes[6] = {0};
        	double hashTimes[6] = {0};
        	double joinTimes[6] = {0};
        	double lininsertTimes[6] = {0};
        	double linupdateTimes[6] = {0};
        	double lindeleteTimes[6] = {0};
        	double linaggregateTimes[6] = {0};
        	double lingroupByTimes[6] = {0};
        	double linselectTimes[6] = {0};
        	double lincontTimes[6] = {0};
        	double linsmallTimes[6] = {0};
        	double linhashTimes[6] = {0};
        	double linalmostAllTimes[6] = {0};
        	double linjoinTimes[6] = {0};
        	time_t startTime, endTime;
        	uint8_t* row = (uint8_t*)malloc(BLOCK_DATA_SIZE);
        	const char* text = "You would measure time the measureless and the immeasurable.";

    		for(int j = 0; j < 1; j++){ //want to average 5 trials
    			//testRound = numInnerTests;
    			if(testRound < numInnerTests){
    				//high = testSize/20*(testRound+1);
				high = (testRound+1)*500;
				//high = testSize - (testRound)*5000;
				if(testRound == numInnerTests - 2){
					high = testSize - 5000;
					printf("95%\n", high);
				}
				else if(testRound == numInnerTests -1){
					high = 5000;
					printf("5%\n", high);
				}
				else if(testRound == numInnerTests -3){
					high = 100;
					printf("100 rows\n", high);
				}

        			//do an aggregate
    				startTime = clock();
    				selectRows(enclave_id, (int*)&status, "testTable", 1, condition1, 3, -1, -1, 0);
    				endTime = clock();
    				linaggregateTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
    		        deleteTable(enclave_id, (int*)&status, "ReturnTable");
    //int selectRows(char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice) {

        			//do a group by aggregate
    				startTime = clock();
    				selectRows(enclave_id, (int*)&status, "testTable", 1, gapCond1, 3, 3, -1, 0);
    				endTime = clock();
    				lingroupByTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
    		        //printTable(enclave_id, (int*)&status, "ReturnTable");
    		        deleteTable(enclave_id, (int*)&status, "ReturnTable");

        			//select
    				startTime = clock();
    				selectRows(enclave_id, (int*)&status, "testTable", -1, gapCond1, -1, -1, -1, 0);
    				endTime = clock();
    				linselectTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
    		        //printTable(enclave_id, (int*)&status, "ReturnTable");
    		        deleteTable(enclave_id, (int*)&status, "ReturnTable");


    				startTime = clock();
    				selectRows(enclave_id, (int*)&status, "testTable", -1, condition2, -1, -1, 1, 0);//continuous
    				endTime = clock();
    				lincontTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
    		        deleteTable(enclave_id, (int*)&status, "ReturnTable");
    				startTime = clock();
    				indexSelect(enclave_id, (int*)&status, tableName, -1, condition2, -1, -1, 1, low, high,0);
    				endTime = clock();
    				contTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
    		        deleteTable(enclave_id, (int*)&status, "ReturnTable");

    				startTime = clock();
    				selectRows(enclave_id, (int*)&status, "testTable", -1, gapCond1, -1, -1, 3, 0);//hash
    				endTime = clock();
    				linhashTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
    		        deleteTable(enclave_id, (int*)&status, "ReturnTable");

    				startTime = clock();
    				indexSelect(enclave_id, (int*)&status, tableName, -1, gapCond1, -1, -1, 3, low, high,0);
    				endTime = clock();
    				hashTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
    		        deleteTable(enclave_id, (int*)&status, "ReturnTable");

    		        //if(testRound >= numInnerTests - 3){
        				startTime = clock();
        				selectRows(enclave_id, (int*)&status, "testTable", -1, gapCond1, -1, -1, 4, 0);//almost all
        				endTime = clock();
        				linalmostAllTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        		        deleteTable(enclave_id, (int*)&status, "ReturnTable");
    		        //}

    		        //if(testSize < 1500){
        				startTime = clock();
        				selectRows(enclave_id, (int*)&status, "testTable", -1, gapCond1, -1, -1, 2, 0);//small
        				endTime = clock();
        				linsmallTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        		        deleteTable(enclave_id, (int*)&status, "ReturnTable");

        				startTime = clock();
        				indexSelect(enclave_id, (int*)&status, tableName, -1, gapCond1, -1, -1, 2, low, high, 0);
        				endTime = clock();
        				smallTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        		        deleteTable(enclave_id, (int*)&status, "ReturnTable");
/*
    	    			//join
    					//startTime = clock();
    			        //joinTables(enclave_id, (int*)&status, "jTable", "testTable", 1, 1, -1, -1);
    					//endTime = clock();
    					//linjoinTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
    	    	        //deleteTable(enclave_id, (int*)&status, "JoinReturn");
    		        //}
*/
        			//do an aggregate
    				startTime = clock();
    				indexSelect(enclave_id, (int*)&status, tableName, 1, gapCond1, 3, -1, -1, low, high, 0);
    				endTime = clock();
    				aggregateTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
    		        deleteTable(enclave_id, (int*)&status, "ReturnTable");
    //int selectRows(char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice) {

        			//do a group by aggregate
    				startTime = clock();
    				indexSelect(enclave_id, (int*)&status, tableName, 1, gapCond1, 3, 3, -1, low, high, 0);
    				endTime = clock();
    				groupByTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
    		        deleteTable(enclave_id, (int*)&status, "ReturnTable");

        			//select
    				startTime = clock();
    				indexSelect(enclave_id, (int*)&status, tableName, -1, gapCond1, -1, -1, -1, low, high, 0);
    				endTime = clock();
    				selectTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
    		        deleteTable(enclave_id, (int*)&status, "ReturnTable");
/*
        			//join
    				//startTime = clock();
    		        //joinTables(enclave_id, (int*)&status, "jIndex", tableName, 1, 1, low, high);
    				//endTime = clock();
    				//joinTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        	        //deleteTable(enclave_id, (int*)&status, "JoinReturn");

*/
    			}
    			else{
    				high = 900;
       		        //printTable(enclave_id, (int*)&status, "testTable");
            			//do an insertion
        				row[0] = 'a';
        				memcpy(&row[1], &testSize, 4);
        				int temp = testSize/100;
        				memcpy(&row[5], &temp, 4);
        				if((testSize)%2 == 0) row[9] = 'a';
        				else if((testSize)%3 == 0) row[9] = 'b';
        				else row[9]= 'c';
        				memcpy(&row[10], text, strlen(text)+1);

        		        //printTable(enclave_id, (int*)&status, "testTable");
        				//printf("here\n");
        				//do an update
        				int updateVal = 313;

        				startTime = clock();
        		        updateRows(enclave_id, (int*)&status, "testTable", condition1, 2, (uint8_t*)&updateVal, -1, -1);
        				endTime = clock();
        				linupdateTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        		        //printTable(enclave_id, (int*)&status, "testTable");

            			//do an aggregate
        				startTime = clock();
        				selectRows(enclave_id, (int*)&status, "testTable", 1, condition1, 3, -1, -1, 0);
        				endTime = clock();
        				linaggregateTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        		        deleteTable(enclave_id, (int*)&status, "ReturnTable");
        //int selectRows(char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice) {


            			//do a group by aggregate
        				startTime = clock();
        				selectRows(enclave_id, (int*)&status, "testTable", 1, condition1, 3, 3, -1, 0);
        				endTime = clock();
        				lingroupByTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        		        //printTable(enclave_id, (int*)&status, "ReturnTable");
        		        deleteTable(enclave_id, (int*)&status, "ReturnTable");

            			//select
        				startTime = clock();
        				selectRows(enclave_id, (int*)&status, "testTable", -1, condition1, -1, -1, -1, 0);
        				endTime = clock();
        				linselectTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        		        //printTable(enclave_id, (int*)&status, "ReturnTable");
        		        deleteTable(enclave_id, (int*)&status, "ReturnTable");

        		        //if(testSize < 1500){
        	    			//join
        				//	startTime = clock();
        			    //    joinTables(enclave_id, (int*)&status, "jTable", "testTable", 1, 1, -1, -1);
        			//		endTime = clock();
        			//		linjoinTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        	    	 //       deleteTable(enclave_id, (int*)&status, "JoinReturn");
        		     //   }

        				startTime = clock();
        				insertRow(enclave_id, (int*)&status, "testTable", row, -1);
        				endTime = clock();
        				lininsertTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);

            	        //delete rows
            	        printf("DELETE\n");
        				startTime = clock();
        		        deleteRows(enclave_id, (int*)&status, "testTable", condition1, -1, -1);
        				endTime = clock();
        				lindeleteTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);

            			//do all the same stuff for an index
            	        //
            	        //
            	        //
            	        printf("switching to Index\n");
            			//create table of size testSize

            			//do an update
        				startTime = clock();
        		        updateRows(enclave_id, (int*)&status, tableName, condition1, 2, (uint8_t*)&updateVal, low, high);
        				endTime = clock();
        				updateTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);

        		        //small select
        				startTime = clock();
        				indexSelect(enclave_id, (int*)&status, tableName, -1, gapCond1, -1, -1, 2, low, high, 0);
        				endTime = clock();
        				smallTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        		        deleteTable(enclave_id, (int*)&status, "ReturnTable");


            			//do an aggregate
        				startTime = clock();
        				indexSelect(enclave_id, (int*)&status, tableName, 1, condition1, 3, -1, -1, low, high, 0);
        				endTime = clock();
        				aggregateTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        		        deleteTable(enclave_id, (int*)&status, "ReturnTable");
        //int selectRows(char* tableName, int colChoice, Condition c, int aggregate, int groupCol, int algChoice) {

            			//do a group by aggregate
        				startTime = clock();
        				indexSelect(enclave_id, (int*)&status, tableName, 1, condition1, 3, 3, -1, low, high, 0);
        				endTime = clock();
        				groupByTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        		        deleteTable(enclave_id, (int*)&status, "ReturnTable");

            			//select
        				startTime = clock();
        				indexSelect(enclave_id, (int*)&status, tableName, -1, condition1, -1, -1, -1, low, high, 0);
        				endTime = clock();
        				selectTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        		        deleteTable(enclave_id, (int*)&status, "ReturnTable");

            			//join
        				//startTime = clock();
        		        //joinTables(enclave_id, (int*)&status, "jIndex", tableName, 1, 1, low, high);
        				//endTime = clock();
        				//joinTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
            	        //deleteTable(enclave_id, (int*)&status, "JoinReturn");


            	        printf("inserting\n");
            			//do an insertion
        				startTime = clock();
        				for(int q = 0; q < 5; q++){
            				insertRow(enclave_id, (int*)&status, tableName, row, testSize);
        				}
        				endTime = clock();
        				insertTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        				insertTimes[j]/=5;
            	        printf("deleting\n");
            	        //delete rows
        				startTime = clock();
        				for(int q = 0; q < 5; q++){//printf("del %d\n", q);
            		        deleteRows(enclave_id, (int*)&status, tableName, noCondition, low, low+2);
        				}
        				endTime = clock();
        				deleteTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        				deleteTimes[j]/=5;
        				//reuse linsmallTimes and linhashTimes for linear insert/delete times
            	        printf("inserting\n");
            			//do an insertion
        				startTime = clock();
        				for(int q = 0; q < 5; q++){
            				insertLinRowFast(enclave_id, (int*)&status, "testTable", row);
        				}
        				endTime = clock();
        				linsmallTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        				linsmallTimes[j]/=5;
            	        printf("deleting\n");
            	        //delete rows
        				startTime = clock();
        				for(int q = 0; q < 5; q++){//printf("del %d\n", q);
            		        deleteRows(enclave_id, (int*)&status, "testTable", noCondition, low, high);
        				}
        				endTime = clock();
        				linhashTimes[j] = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        				linhashTimes[j]/=5;
        				printf("end\n");
    			}




    		}
    		free(row);
    		for(int j = 0; j < 5; j++){
            	insertTimes[5] += insertTimes[j];
            	updateTimes[5] += updateTimes[j];
            	deleteTimes[5] += deleteTimes[j];
            	aggregateTimes[5] += aggregateTimes[j];
            	groupByTimes[5] += groupByTimes[j];
            	selectTimes[5] += selectTimes[j];
            	contTimes[5] += contTimes[j];
            	smallTimes[5] += smallTimes[j];
            	hashTimes[5] += hashTimes[j];
            	joinTimes[5] += joinTimes[j];
            	lininsertTimes[5] += lininsertTimes[j];
            	linupdateTimes[5] += linupdateTimes[j];
            	lindeleteTimes[5] += lindeleteTimes[j];
            	linaggregateTimes[5] += linaggregateTimes[j];
            	lingroupByTimes[5] += lingroupByTimes[j];
            	linselectTimes[5] += linselectTimes[j];
            	lincontTimes[5] += lincontTimes[j];
            	linsmallTimes[5] += linsmallTimes[j];
            	linhashTimes[5] += linhashTimes[j];
            	linalmostAllTimes[5] += linalmostAllTimes[j];
            	linjoinTimes[5] += linjoinTimes[j];
    		}
        	insertTimes[5] /= 5;
        	updateTimes[5] /= 5;
        	deleteTimes[5] /= 5;
        	aggregateTimes[5] /= 5;
        	groupByTimes[5] /= 5;
        	selectTimes[5] /= 5;
        	contTimes[5] /= 5;
        	smallTimes[5] /= 5;
        	hashTimes[5] /= 5;
        	joinTimes[5] /= 5;
        	lininsertTimes[5] /= 5;
        	linupdateTimes[5] /= 5;
        	lindeleteTimes[5] /= 5;
        	linaggregateTimes[5] /= 5;
        	lingroupByTimes[5] /= 5;
        	linselectTimes[5] /= 5;
        	lincontTimes[5] /= 5;
        	linsmallTimes[5] /= 5;
        	linhashTimes[5] /= 5;
        	linalmostAllTimes[5] /= 5;
        	linjoinTimes[5] /= 5;
    		printf("insertTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", insertTimes[0], insertTimes[1], insertTimes[2], insertTimes[3], insertTimes[4], insertTimes[5]);
    		printf("updateTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", updateTimes[0], updateTimes[1], updateTimes[2], updateTimes[3], updateTimes[4], updateTimes[5]);
    		printf("deleteTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", deleteTimes[0], deleteTimes[1], deleteTimes[2], deleteTimes[3], deleteTimes[4], deleteTimes[5]);
    		printf("aggregateTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", aggregateTimes[0], aggregateTimes[1], aggregateTimes[2], aggregateTimes[3], aggregateTimes[4], aggregateTimes[5]);
    		printf("groupByTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", groupByTimes[0], groupByTimes[1], groupByTimes[2], groupByTimes[3], groupByTimes[4], groupByTimes[5]);
    		printf("selectTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", selectTimes[0], selectTimes[1], selectTimes[2], selectTimes[3], selectTimes[4], selectTimes[5]);
    		printf("contTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", contTimes[0], contTimes[1], contTimes[2], contTimes[3], contTimes[4], contTimes[5]);
    		printf("smallTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", smallTimes[0], smallTimes[1], smallTimes[2], smallTimes[3], smallTimes[4], smallTimes[5]);
    		printf("hashTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", hashTimes[0], hashTimes[1], hashTimes[2], hashTimes[3], hashTimes[4], hashTimes[5]);
    		printf("joinTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", joinTimes[0], joinTimes[1], joinTimes[2], joinTimes[3], joinTimes[4], joinTimes[5]);
    		printf("lininsertTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", lininsertTimes[0], lininsertTimes[1], lininsertTimes[2], lininsertTimes[3], lininsertTimes[4], lininsertTimes[5]);
    		printf("linupdateTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", linupdateTimes[0], linupdateTimes[1], linupdateTimes[2], linupdateTimes[3], linupdateTimes[4], linupdateTimes[5]);
    		printf("lindeleteTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", lindeleteTimes[0], lindeleteTimes[1], lindeleteTimes[2], lindeleteTimes[3], lindeleteTimes[4], lindeleteTimes[5]);
    		printf("linaggregateTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", linaggregateTimes[0], linaggregateTimes[1], linaggregateTimes[2], linaggregateTimes[3], linaggregateTimes[4], linaggregateTimes[5]);
    		printf("lingroupByTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", lingroupByTimes[0], lingroupByTimes[1], lingroupByTimes[2], lingroupByTimes[3], lingroupByTimes[4], lingroupByTimes[5]);
    		printf("linselectTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", linselectTimes[0], linselectTimes[1], linselectTimes[2], linselectTimes[3], linselectTimes[4], linselectTimes[5]);
    		printf("lincontTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", lincontTimes[0], lincontTimes[1], lincontTimes[2], lincontTimes[3], lincontTimes[4], lincontTimes[5]);
    		printf("linsmallTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", linsmallTimes[0], linsmallTimes[1], linsmallTimes[2], linsmallTimes[3], linsmallTimes[4], linsmallTimes[5]);
    		printf("linhashTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", linhashTimes[0], linhashTimes[1], linhashTimes[2], linhashTimes[3], linhashTimes[4], linhashTimes[5]);
    		printf("linalmostAllTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", linalmostAllTimes[0], linalmostAllTimes[1], linalmostAllTimes[2], linalmostAllTimes[3], linalmostAllTimes[4], linalmostAllTimes[5]);
    		printf("linjoinTimes | %.5f %.5f %.5f %.5f %.5f : %.5f\n", linjoinTimes[0], linjoinTimes[1], linjoinTimes[2], linjoinTimes[3], linjoinTimes[4], linjoinTimes[5]);
		}
	}
    deleteTable(enclave_id, (int*)&status, "jIndex");
    deleteTable(enclave_id, (int*)&status, "jTable");
	deleteTable(enclave_id, (int*)&status, "testTable");
	deleteTable(enclave_id, (int*)&status, tableName);

}


//helpers


/*
 * End Saba's code
 * */


// This sample code doesn't have any recovery/retry mechanisms for the remote
// attestation. Since the enclave can be lost due S3 transitions, apps
// susceptible to S3 transitions should have logic to restart attestation in
// these scenarios.
#define _T(x) x
int main(int argc, char* argv[])
{
    int ret = 0;
    ra_samp_request_header_t *p_msg0_full = NULL;
    ra_samp_response_header_t *p_msg0_resp_full = NULL;
    ra_samp_request_header_t *p_msg1_full = NULL;
    ra_samp_response_header_t *p_msg2_full = NULL;
    sgx_ra_msg3_t *p_msg3 = NULL;
    ra_samp_response_header_t* p_att_result_msg_full = NULL;
    sgx_enclave_id_t enclave_id = 0;
    int enclave_lost_retry_time = 1;
    int busy_retry_time = 4;
    sgx_ra_context_t context = INT_MAX;
    sgx_status_t status = SGX_SUCCESS;
    ra_samp_request_header_t* p_msg3_full = NULL;

    int32_t verify_index = -1;
    int32_t verification_samples = sizeof(msg1_samples)/sizeof(msg1_samples[0]);

    FILE* OUTPUT = stdout;

#define VERIFICATION_INDEX_IS_VALID() (verify_index > 0 && \
                                       verify_index <= verification_samples)
#define GET_VERIFICATION_ARRAY_INDEX() (verify_index-1)

    if(argc > 1)
    {

        verify_index = atoi(argv[1]);

        if( VERIFICATION_INDEX_IS_VALID())
        {
            //fprintf(OUTPUT, "\nVerifying precomputed attestation messages "
            //                "using precomputed values# %d\n", verify_index);
        }
        else
        {
            fprintf(OUTPUT, "\nValid invocations are:\n");
            fprintf(OUTPUT, "\n\tisv_app\n");
            fprintf(OUTPUT, "\n\tisv_app <verification index>\n");
            fprintf(OUTPUT, "\nValid indices are [1 - %d]\n",
                    verification_samples);
            fprintf(OUTPUT, "\nUsing a verification index uses precomputed "
                    "messages to assist debugging the remote attestation "
                    "service provider.\n");
            return -1;
        }
    }

    // Preparation for remote attestation by configuring extended epid group id.
    {
        uint32_t extended_epid_group_id = 0;
        ret = sgx_get_extended_epid_group_id(&extended_epid_group_id);
        if (SGX_SUCCESS != ret)
        {
            ret = -1;
            fprintf(OUTPUT, "\nError, call sgx_get_extended_epid_group_id fail [%s].",
                __FUNCTION__);
            return ret;
        }
        fprintf(OUTPUT, "\nCall sgx_get_extended_epid_group_id success.");

        p_msg0_full = (ra_samp_request_header_t*)
            malloc(sizeof(ra_samp_request_header_t)
            +sizeof(uint32_t));
        if (NULL == p_msg0_full)
        {
            ret = -1;
            goto CLEANUP;
        }
        p_msg0_full->type = TYPE_RA_MSG0;
        p_msg0_full->size = sizeof(uint32_t);

        *(uint32_t*)((uint8_t*)p_msg0_full + sizeof(ra_samp_request_header_t)) = extended_epid_group_id;
        {

            //fprintf(OUTPUT, "\nMSG0 body generated -\n");

            //PRINT_BYTE_ARRAY(OUTPUT, p_msg0_full->body, p_msg0_full->size);

        }
        // The ISV application sends msg0 to the SP.
        // The ISV decides whether to support this extended epid group id.
        //fprintf(OUTPUT, "\nSending msg0 to remote attestation service provider.\n");

        ret = ra_network_send_receive("http://SampleServiceProvider.intel.com/",
            p_msg0_full,
            &p_msg0_resp_full);
        if (ret != 0)
        {
            fprintf(OUTPUT, "\nError, ra_network_send_receive for msg0 failed "
                "[%s].", __FUNCTION__);
            goto CLEANUP;
        }
        //fprintf(OUTPUT, "\nSent MSG0 to remote attestation service.\n");
    }
    // Remote attestation will be initiated the ISV server challenges the ISV
    // app or if the ISV app detects it doesn't have the credentials
    // (shared secret) from a previous attestation required for secure
    // communication with the server.
    {
        // ISV application creates the ISV enclave.
        int launch_token_update = 0;
        sgx_launch_token_t launch_token = {0};
        memset(&launch_token, 0, sizeof(sgx_launch_token_t));
        do
        {
            ret = sgx_create_enclave(_T(ENCLAVE_PATH),
                                     SGX_DEBUG_FLAG,
                                     &launch_token,
                                     &launch_token_update,
                                     &enclave_id, NULL);
            if(SGX_SUCCESS != ret)
            {
                ret = -1;
                fprintf(OUTPUT, "\nError, call sgx_create_enclave fail [%s].",
                        __FUNCTION__);
                goto CLEANUP;
            }
            fprintf(OUTPUT, "\nCall sgx_create_enclave success.");

            ret = enclave_init_ra(enclave_id,
                                  &status,
                                  false,
                                  &context);
        //Ideally, this check would be around the full attestation flow.
        } while (SGX_ERROR_ENCLAVE_LOST == ret && enclave_lost_retry_time--);

        if(SGX_SUCCESS != ret || status)
        {
            ret = -1;
            fprintf(OUTPUT, "\nError, call enclave_init_ra fail [%s].",
                    __FUNCTION__);
            goto CLEANUP;
        }
        fprintf(OUTPUT, "\nCall enclave_init_ra success.");

        // isv application call uke sgx_ra_get_msg1
        p_msg1_full = (ra_samp_request_header_t*)
                      malloc(sizeof(ra_samp_request_header_t)
                             + sizeof(sgx_ra_msg1_t));
        if(NULL == p_msg1_full)
        {
            ret = -1;
            goto CLEANUP;
        }
        p_msg1_full->type = TYPE_RA_MSG1;
        p_msg1_full->size = sizeof(sgx_ra_msg1_t);
        do
        {
            ret = sgx_ra_get_msg1(context, enclave_id, sgx_ra_get_ga,
                                  (sgx_ra_msg1_t*)((uint8_t*)p_msg1_full
                                  + sizeof(ra_samp_request_header_t)));
            sleep(3); // Wait 3s between retries
        } while (SGX_ERROR_BUSY == ret && busy_retry_time--);
        if(SGX_SUCCESS != ret)
        {
            ret = -1;
            fprintf(OUTPUT, "\nError, call sgx_ra_get_msg1 fail [%s].",
                    __FUNCTION__);
            goto CLEANUP;
        }
        else
        {
            //fprintf(OUTPUT, "\nCall sgx_ra_get_msg1 success.\n");

            //fprintf(OUTPUT, "\nMSG1 body generated -\n");

            //PRINT_BYTE_ARRAY(OUTPUT, p_msg1_full->body, p_msg1_full->size);

        }

        if(VERIFICATION_INDEX_IS_VALID())
        {

            memcpy_s(p_msg1_full->body, p_msg1_full->size,
                     msg1_samples[GET_VERIFICATION_ARRAY_INDEX()],
                     p_msg1_full->size);

            fprintf(OUTPUT, "\nInstead of using the recently generated MSG1, "
                            "we will use the following precomputed MSG1 -\n");

            //PRINT_BYTE_ARRAY(OUTPUT, p_msg1_full->body, p_msg1_full->size);
        }


        // The ISV application sends msg1 to the SP to get msg2,
        // msg2 needs to be freed when no longer needed.
        // The ISV decides whether to use linkable or unlinkable signatures.
        //fprintf(OUTPUT, "\nSending msg1 to remote attestation service provider."
          //              "Expecting msg2 back.\n");


        ret = ra_network_send_receive("http://SampleServiceProvider.intel.com/",
                                      p_msg1_full,
                                      &p_msg2_full);

        if(ret != 0 || !p_msg2_full)
        {
            fprintf(OUTPUT, "\nError, ra_network_send_receive for msg1 failed "
                            "[%s].", __FUNCTION__);
            if(VERIFICATION_INDEX_IS_VALID())
            {
                fprintf(OUTPUT, "\nBecause we are in verification mode we will "
                                "ignore this error.\n");
                fprintf(OUTPUT, "\nInstead, we will pretend we received the "
                                "following MSG2 - \n");

                SAFE_FREE(p_msg2_full);
                ra_samp_response_header_t* precomputed_msg2 =
                    (ra_samp_response_header_t*)msg2_samples[
                        GET_VERIFICATION_ARRAY_INDEX()];
                const size_t msg2_full_size = sizeof(ra_samp_response_header_t)
                                              +  precomputed_msg2->size;
                p_msg2_full =
                    (ra_samp_response_header_t*)malloc(msg2_full_size);
                if(NULL == p_msg2_full)
                {
                    ret = -1;
                    goto CLEANUP;
                }
                memcpy_s(p_msg2_full, msg2_full_size, precomputed_msg2,
                         msg2_full_size);

                //PRINT_BYTE_ARRAY(OUTPUT, p_msg2_full,
                //                 sizeof(ra_samp_response_header_t)
                //                 + p_msg2_full->size);
            }
            else
            {
                goto CLEANUP;
            }
        }
        else
        {
            // Successfully sent msg1 and received a msg2 back.
            // Time now to check msg2.
            if(TYPE_RA_MSG2 != p_msg2_full->type)
            {

                fprintf(OUTPUT, "\nError, didn't get MSG2 in response to MSG1. "
                                "[%s].", __FUNCTION__);

                if(VERIFICATION_INDEX_IS_VALID())
                {
                    fprintf(OUTPUT, "\nBecause we are in verification mode we "
                                    "will ignore this error.");
                }
                else
                {
                    goto CLEANUP;
                }
            }

            //fprintf(OUTPUT, "\nSent MSG1 to remote attestation service "
            //                "provider. Received the following MSG2:\n");
            //PRINT_BYTE_ARRAY(OUTPUT, p_msg2_full,
             //                sizeof(ra_samp_response_header_t)
              //               + p_msg2_full->size);

            //fprintf(OUTPUT, "\nA more descriptive representation of MSG2:\n");
            //PRINT_ATTESTATION_SERVICE_RESPONSE(OUTPUT, p_msg2_full);

            if( VERIFICATION_INDEX_IS_VALID() )
            {
                // The response should match the precomputed MSG2:
                ra_samp_response_header_t* precomputed_msg2 =
                    (ra_samp_response_header_t *)
                    msg2_samples[GET_VERIFICATION_ARRAY_INDEX()];
                if(memcmp( precomputed_msg2, p_msg2_full,
                   sizeof(ra_samp_response_header_t) + p_msg2_full->size))
                {/*
                    fprintf(OUTPUT, "\nVerification ERROR. Our precomputed "
                                    "value for MSG2 does NOT match.\n");
                    fprintf(OUTPUT, "\nPrecomputed value for MSG2:\n");
                    PRINT_BYTE_ARRAY(OUTPUT, precomputed_msg2,
                                     sizeof(ra_samp_response_header_t)
                                     + precomputed_msg2->size);
                    fprintf(OUTPUT, "\nA more descriptive representation "
                                    "of precomputed value for MSG2:\n");
                    PRINT_ATTESTATION_SERVICE_RESPONSE(OUTPUT,
                                                       precomputed_msg2);*/
                }
                else
                {
                    fprintf(OUTPUT, "\nVerification COMPLETE. Remote "
                                    "attestation service provider generated a "
                                    "matching MSG2.\n");
                }
            }

        }

        sgx_ra_msg2_t* p_msg2_body = (sgx_ra_msg2_t*)((uint8_t*)p_msg2_full
                                      + sizeof(ra_samp_response_header_t));


        uint32_t msg3_size = 0;
        if( VERIFICATION_INDEX_IS_VALID())
        {
            // We cannot generate a valid MSG3 using the precomputed messages
            // we have been using. We will use the precomputed msg3 instead.
            msg3_size = MSG3_BODY_SIZE;
            p_msg3 = (sgx_ra_msg3_t*)malloc(msg3_size);
            if(NULL == p_msg3)
            {
                ret = -1;
                goto CLEANUP;
            }
            memcpy_s(p_msg3, msg3_size,
                     msg3_samples[GET_VERIFICATION_ARRAY_INDEX()], msg3_size);
            fprintf(OUTPUT, "\nBecause MSG1 was a precomputed value, the MSG3 "
                            "we use will also be. PRECOMPUTED MSG3 - \n");
        }
        else
        {
            busy_retry_time = 2;
            // The ISV app now calls uKE sgx_ra_proc_msg2,
            // The ISV app is responsible for freeing the returned p_msg3!!
            do
            {
                ret = sgx_ra_proc_msg2(context,
                                   enclave_id,
                                   sgx_ra_proc_msg2_trusted,
                                   sgx_ra_get_msg3_trusted,
                                   p_msg2_body,
                                   p_msg2_full->size,
                                   &p_msg3,
                                   &msg3_size);
            } while (SGX_ERROR_BUSY == ret && busy_retry_time--);
            if(!p_msg3)
            {
                fprintf(OUTPUT, "\nError, call sgx_ra_proc_msg2 fail. "
                                "p_msg3 = 0x%p [%s].", p_msg3, __FUNCTION__);
                ret = -1;
                goto CLEANUP;
            }
            if(SGX_SUCCESS != (sgx_status_t)ret)
            {
                fprintf(OUTPUT, "\nError, call sgx_ra_proc_msg2 fail. "
                                "ret = 0x%08x [%s].", ret, __FUNCTION__);
                ret = -1;
                goto CLEANUP;
            }
            else
            {
                fprintf(OUTPUT, "\nCall sgx_ra_proc_msg2 success.\n");
                fprintf(OUTPUT, "\nMSG3 - \n");
            }
        }

        //PRINT_BYTE_ARRAY(OUTPUT, p_msg3, msg3_size);

        p_msg3_full = (ra_samp_request_header_t*)malloc(
                       sizeof(ra_samp_request_header_t) + msg3_size);
        if(NULL == p_msg3_full)
        {
            ret = -1;
            goto CLEANUP;
        }
        p_msg3_full->type = TYPE_RA_MSG3;
        p_msg3_full->size = msg3_size;
        if(memcpy_s(p_msg3_full->body, msg3_size, p_msg3, msg3_size))
        {
            fprintf(OUTPUT,"\nError: INTERNAL ERROR - memcpy failed in [%s].",
                    __FUNCTION__);
            ret = -1;
            goto CLEANUP;
        }

        // The ISV application sends msg3 to the SP to get the attestation
        // result message, attestation result message needs to be freed when
        // no longer needed. The ISV service provider decides whether to use
        // linkable or unlinkable signatures. The format of the attestation
        // result is up to the service provider. This format is used for
        // demonstration.  Note that the attestation result message makes use
        // of both the MK for the MAC and the SK for the secret. These keys are
        // established from the SIGMA secure channel binding.
        ret = ra_network_send_receive("http://SampleServiceProvider.intel.com/",
                                      p_msg3_full,
                                      &p_att_result_msg_full);
        if(ret || !p_att_result_msg_full)
        {
            ret = -1;
            fprintf(OUTPUT, "\nError, sending msg3 failed [%s].", __FUNCTION__);
            goto CLEANUP;
        }


        sample_ra_att_result_msg_t * p_att_result_msg_body =
            (sample_ra_att_result_msg_t *)((uint8_t*)p_att_result_msg_full
                                           + sizeof(ra_samp_response_header_t));
        if(TYPE_RA_ATT_RESULT != p_att_result_msg_full->type)
        {
            ret = -1;
            fprintf(OUTPUT, "\nError. Sent MSG3 successfully, but the message "
                            "received was NOT of type att_msg_result. Type = "
                            "%d. [%s].", p_att_result_msg_full->type,
                             __FUNCTION__);
            goto CLEANUP;
        }
        else
        {
            fprintf(OUTPUT, "\nSent MSG3 successfully. Received an attestation "
                            "result message back\n.");
            if( VERIFICATION_INDEX_IS_VALID() )
            {
                if(memcmp(p_att_result_msg_full->body,
                        attestation_msg_samples[GET_VERIFICATION_ARRAY_INDEX()],
                        p_att_result_msg_full->size) )
                {
                    fprintf(OUTPUT, "\nSent MSG3 successfully. Received an "
                                    "attestation result message back that did "
                                    "NOT match the expected value.\n");
                    fprintf(OUTPUT, "\nEXPECTED ATTESTATION RESULT -");
                    PRINT_BYTE_ARRAY(OUTPUT,
                        attestation_msg_samples[GET_VERIFICATION_ARRAY_INDEX()],
                        p_att_result_msg_full->size);
                }
            }
        }

        fprintf(OUTPUT, "\nATTESTATION RESULT RECEIVED - ");
        //PRINT_BYTE_ARRAY(OUTPUT, p_att_result_msg_full->body,
        //                 p_att_result_msg_full->size);


        if( VERIFICATION_INDEX_IS_VALID() )
        {
            fprintf(OUTPUT, "\nBecause we used precomputed values for the "
                            "messages, the attestation result message will "
                            "not pass further verification tests, so we will "
                            "skip them.\n");
            goto CLEANUP;
        }

        // Check the MAC using MK on the attestation result message.
        // The format of the attestation result message is ISV specific.
        // This is a simple form for demonstration. In a real product,
        // the ISV may want to communicate more information.
        ret = verify_att_result_mac(enclave_id,
                &status,
                context,
                (uint8_t*)&p_att_result_msg_body->platform_info_blob,
                sizeof(ias_platform_info_blob_t),
                (uint8_t*)&p_att_result_msg_body->mac,
                sizeof(sgx_mac_t));
        if((SGX_SUCCESS != ret) ||
           (SGX_SUCCESS != status))
        {
            ret = -1;
            fprintf(OUTPUT, "\nError: INTEGRITY FAILED - attestation result "
                            "message MK based cmac failed in [%s].",
                            __FUNCTION__);
            goto CLEANUP;
        }

        bool attestation_passed = true;
        // Check the attestation result for pass or fail.
        // Whether attestation passes or fails is a decision made by the ISV Server.
        // When the ISV server decides to trust the enclave, then it will return success.
        // When the ISV server decided to not trust the enclave, then it will return failure.
        if(0 != p_att_result_msg_full->status[0]
           || 0 != p_att_result_msg_full->status[1])
        {
            fprintf(OUTPUT, "\nError, attestation result message MK based cmac "
                            "failed in [%s].", __FUNCTION__);
            attestation_passed = false;
        }

        // The attestation result message should contain a field for the Platform
        // Info Blob (PIB).  The PIB is returned by attestation server in the attestation report.
        // It is not returned in all cases, but when it is, the ISV app
        // should pass it to the blob analysis API called sgx_report_attestation_status()
        // along with the trust decision from the ISV server.
        // The ISV application will take action based on the update_info.
        // returned in update_info by the API.  
        // This call is stubbed out for the sample.
        // 
        // sgx_update_info_bit_t update_info;
        // ret = sgx_report_attestation_status(
        //     &p_att_result_msg_body->platform_info_blob,
        //     attestation_passed ? 0 : 1, &update_info);

        // Get the shared secret sent by the server using SK (if attestation
        // passed)
        if(attestation_passed)
        {
            ret = put_secret_data(enclave_id,
                                  &status,
                                  context,
                                  p_att_result_msg_body->secret.payload,
                                  p_att_result_msg_body->secret.payload_size,
                                  p_att_result_msg_body->secret.payload_tag);
            if((SGX_SUCCESS != ret)  || (SGX_SUCCESS != status))
            {
                fprintf(OUTPUT, "\nError, attestation result message secret "
                                "using SK based AESGCM failed in [%s]. ret = "
                                "0x%0x. status = 0x%0x", __FUNCTION__, ret,
                                 status);
                goto CLEANUP;
            }
        }
        fprintf(OUTPUT, "\nSecret successfully received from server.\n");
        fprintf(OUTPUT, "\nRemote attestation success!\n");
    }

    //TODO: My untrusted application code goes here
    /*
     *
     *
     *Begin Saba's Code
     *
     *
	*/
    {
    	//free stuff used before
    	ra_free_network_response_buffer(p_msg0_resp_full);
    	ra_free_network_response_buffer(p_msg2_full);
    	ra_free_network_response_buffer(p_att_result_msg_full);

    	    // p_msg3 is malloc'd by the untrusted KE library. App needs to free.
    	SAFE_FREE(p_msg3);
    	SAFE_FREE(p_msg3_full);
    	SAFE_FREE(p_msg1_full);
    	SAFE_FREE(p_msg0_full);


    	total_init(enclave_id, &status);
        if(status != SGX_SUCCESS){
        	printf("key initialization failed %d.\n", status);
        	goto CLEANUP;
        }

		/**
		 * connect to db
		 * 考虑一下执行顺序，只有reopen需要去换
		 * 而不是在 reopn 的过程中自行在 sgx 的堆上 malloc
		 */
    	ConnectDB(enclave_id, status);

    	//trigger oram initialization
    	ra_samp_response_header_t *oramInitMsg_resp = NULL;
        ra_samp_request_header_t* p_oramInitMsg = (ra_samp_request_header_t*) malloc(sizeof(ra_samp_request_header_t));
        if (NULL == p_oramInitMsg)
        {
            ret = -1;
            goto CLEANUP;
        }
        p_oramInitMsg->type = TYPE_TREE_ORAM_INIT;
        p_oramInitMsg->size = 0;
        ret = ra_network_send_receive("http://SampleServiceProvider.intel.com/",
            p_oramInitMsg,
            &oramInitMsg_resp);
        if (ret != 0)
        {
            //fprintf(OUTPUT, "\nError, ra_network_send_receive for oramInitMsg failed "
             //   "[%s].", __FUNCTION__);
            goto CLEANUP;
        }
        //fprintf(OUTPUT, "\nSent oram init to remote attestation service.\n");

        //now use the request in oramInitMsg to initialize oram

        unsigned int *oramCapacity = (unsigned int*)malloc(sizeof(int));
        memcpy(oramCapacity, oramInitMsg_resp->body, sizeof(int));

        //real world query tests
        //PICK EXPERIMENT TO RUN HERE
		// OpenDB1thTable(enclave_id, status);
		SelectTable(enclave_id, status);
		// PersistExample(enclave_id, status);
		// DBContinueAT(enclave_id, status);
        //nasdaqTables(enclave_id, status); //2048	
        //complaintTables(enclave_id, status); //4096	
        //flightTables(enclave_id, status); //512 (could be less, but we require 512 minimum)	
        // BDB1Index(enclave_id, status);//512		
        // BDB1Linear(enclave_id, status);//512		
        //BDB2(enclave_id, status, 0);//2048		
        //BDB2Index(enclave_id, status, 0);//2048	
        //BDB3(enclave_id, status, 0);//2048		
        //BDB2(enclave_id, status, 1);//2048 (baseline)	
        //BDB3(enclave_id, status, 1);//2048 (baseline)	
        //basicTests(enclave_id, status);//512		
		//fabTests(enclave_id, status);//512		
        // joinTests(enclave_id, status);//512		
        //workloadTests(enclave_id, status);//512	
        //insdelScaling(enclave_id, status);//512	


/*
	//test for sophos - linear
	char* tn = "table";
	int stid = -1;
	Schema slimSchema;
	slimSchema.numFields = 2;
	slimSchema.fieldOffsets[0] = 0;
	slimSchema.fieldOffsets[1] = 1;
	slimSchema.fieldSizes[0] = 1;
	slimSchema.fieldSizes[1] = 4;
	slimSchema.fieldTypes[0] = CHAR;
	slimSchema.fieldTypes[1] = INTEGER;
	uint8_t* smallR = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	smallR[0] = 1;
	createTable(enclave_id, (int*)&status, &slimSchema, tn, strlen(tn), TYPE_LINEAR_SCAN, 1400000, &stid);
		printf("created table\n");
	for(int c = 0; c < 1400000; c++){
		memcpy(&smallR[1], &c, 4);
		//insertIndexRowFast(enclave_id, (int*)&status, tn, smallR, c);
		opOneLinearScanBlock(enclave_id, (int*)&status, stid, c, (Linear_Scan_Block*)smallR, 1);
		incrementNumRows(enclave_id, (int*)&status, stid);
		if(c % 100000 == 0) printf("pulse %d %d\n", smallR[1], c);
	}
	time_t startTime, endTime;
	double elapsedTime;
		
	Condition cond;
	cond.numClauses = 1;
	cond.fieldNums[0] = 1;
	cond.conditionType[0] = -1;
	cond.values[0] = (uint8_t*)malloc(4);
	cond.nextCondition = NULL;
	int v = 1000000;
	memcpy(cond.values[0], &v, 4);
	

	v = 1000;
        startTime = clock();
        selectRows(enclave_id, (int*)&status, tn, 1, cond, -1, -1, 1, 0);
        endTime = clock();
        elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        printf("query 1000 rt: %.5f\n", elapsedTime);	
	fflush(stdout);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
	deleteTable(enclave_id, (int*)&status, "ReturnTable");
	v = 100;
        startTime = clock();
        selectRows(enclave_id, (int*)&status, tn, 1, cond, -1, -1, 1, 0);
        endTime = clock();
        elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        printf("query 100 rt: %.5f\n", elapsedTime);	
	fflush(stdout);
	deleteTable(enclave_id, (int*)&status, "ReturnTable");
	v = 10;
        startTime = clock();
        selectRows(enclave_id, (int*)&status, tn, 1, cond, -1, -1, 1, 0);
        endTime = clock();
        elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        printf("query 10 rt: %.5f\n", elapsedTime);	
	fflush(stdout);
	deleteTable(enclave_id, (int*)&status, "ReturnTable");
	v = 100000;
        startTime = clock();
        selectRows(enclave_id, (int*)&status, tn, 1, cond, -1, -1, 1, 0);
        endTime = clock();
        elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        printf("query 100000 rt: %.5f\n", elapsedTime);	
	fflush(stdout);
	deleteTable(enclave_id, (int*)&status, "ReturnTable");
	v = 10000;
        startTime = clock();
        selectRows(enclave_id, (int*)&status, tn, 1, cond, -1, -1, 1, 0);
        endTime = clock();
        elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        printf("query 10000 rt: %.5f\n", elapsedTime);	
	fflush(stdout);
	deleteTable(enclave_id, (int*)&status, "ReturnTable");
*/	
/*
	//test for sophos
	char* tn = "table";
	int stid = -1;
	Schema slimSchema;
	slimSchema.numFields = 2;
	slimSchema.fieldOffsets[0] = 0;
	slimSchema.fieldOffsets[1] = 1;
	slimSchema.fieldSizes[0] = 1;
	slimSchema.fieldSizes[1] = 4;
	slimSchema.fieldTypes[0] = CHAR;
	slimSchema.fieldTypes[1] = INTEGER;
	uint8_t* smallR = (uint8_t*)malloc(BLOCK_DATA_SIZE);
	smallR[0] = 1;
	createTable(enclave_id, (int*)&status, &slimSchema, tn, strlen(tn), TYPE_TREE_ORAM, 1400000, &stid);
		printf("created table\n");
	for(int c = 0; c < 1400000; c++){
		memcpy(&smallR[1], &c, 4);
		insertIndexRowFast(enclave_id, (int*)&status, tn, smallR, c);
		//opOneLinearScanBlock(enclave_id, (int*)&status, stid, c, (Linear_Scan_Block*)smallR, 1);
		//incrementNumRows(enclave_id, (int*)&status, stid);
		if(c % 100000 == 0) printf("pulse %d %d\n", smallR[1], c);
	}
	time_t startTime, endTime;
	double elapsedTime;
		
	Condition cond;
	cond.numClauses = 1;
	cond.fieldNums[0] = 1;
	cond.conditionType[0] = -1;
	cond.values[0] = (uint8_t*)malloc(4);
	cond.nextCondition = NULL;
	int v = 1000000;
	memcpy(cond.values[0], &v, 4);
	

	v = 1000;
        startTime = clock();
        indexSelect(enclave_id, (int*)&status, tn, 1, cond, -1, -1, 2, 0, v, 0);
        endTime = clock();
        elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        printf("query 1000 rt: %.5f\n", elapsedTime);	
	fflush(stdout);
	//printTable(enclave_id, (int*)&status, "ReturnTable");
	deleteTable(enclave_id, (int*)&status, "ReturnTable");
	v = 100;
        startTime = clock();
        indexSelect(enclave_id, (int*)&status, tn, 1, cond, -1, -1, 2, 0, v, 0);
        endTime = clock();
        elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        printf("query 100 rt: %.5f\n", elapsedTime);	
	fflush(stdout);
	deleteTable(enclave_id, (int*)&status, "ReturnTable");
	v = 10;
        startTime = clock();
        indexSelect(enclave_id, (int*)&status, tn, 1, cond, -1, -1, 2, 0, v, 0);
        endTime = clock();
        elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        printf("query 10 rt: %.5f\n", elapsedTime);	
	fflush(stdout);
	deleteTable(enclave_id, (int*)&status, "ReturnTable");
	v = 100000;
        startTime = clock();
        indexSelect(enclave_id, (int*)&status, tn, 1, cond, -1, -1, 2, 0, v, 0);
        endTime = clock();
        elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        printf("query 100000 rt: %.5f\n", elapsedTime);	
	fflush(stdout);
	deleteTable(enclave_id, (int*)&status, "ReturnTable");
	v = 10000;
        startTime = clock();
        indexSelect(enclave_id, (int*)&status, tn, 1, cond, -1, -1, 2, 0, v, 0);
        endTime = clock();
        elapsedTime = (double)(endTime - startTime)/(CLOCKS_PER_SEC);
        printf("query 10000 rt: %.5f\n", elapsedTime);	
	fflush(stdout);
	deleteTable(enclave_id, (int*)&status, "ReturnTable");
*/
        /*
        //rename test
        createTestTable(enclave_id, (int*)&status, "table1", 10);
        printTable(enclave_id, (int*)&status, "table1");
        char* newName = "t2";
        renameTable(enclave_id, (int*)&status, "table1", newName);
        printTable(enclave_id, (int*)&status, "t2");
*/



/*
    	//printf("starting");fflush(stdout);
    	char delTestName[20];
		sprintf(delTestName, "testTable%d", 500);
        //loadIndexTable(enclave_id, (int*)&status, 500);
    	createTestTableIndex(enclave_id, (int*)&status, delTestName, 1000);printf("del0");fflush(stdout);
        //indexSelect(enclave_id, (int*)&status, delTestName, -1, noCondition, -1, -1, -1, low, high);
    	//printTable(enclave_id, (int*)&status, "ReturnTable");
    	//deleteTable(enclave_id, (int*)&status, "ReturnTable");

        deleteRows(enclave_id, (int*)&status, delTestName, condition1, low, high);printf("del1\n");fflush(stdout);
        deleteRows(enclave_id, (int*)&status, delTestName, condition1, low, high);printf("del2\n");fflush(stdout);
        deleteRows(enclave_id, (int*)&status, delTestName, condition1, low, high);printf("del3\n");fflush(stdout);
        deleteRows(enclave_id, (int*)&status, delTestName, condition1, low, high);printf("del4\n");fflush(stdout);
        deleteRows(enclave_id, (int*)&status, delTestName, condition1, low, high);printf("del5\n");fflush(stdout);
        deleteRows(enclave_id, (int*)&status, delTestName, condition1, low, high);printf("del6\n");fflush(stdout);
        deleteRows(enclave_id, (int*)&status, delTestName, condition1, low, high);printf("del1\n");fflush(stdout);
        deleteRows(enclave_id, (int*)&status, delTestName, condition1, low, high);printf("del2\n");fflush(stdout);
        deleteRows(enclave_id, (int*)&status, delTestName, condition1, low, high);printf("del3\n");fflush(stdout);
        deleteRows(enclave_id, (int*)&status, delTestName, condition1, low, high);printf("del4\n");fflush(stdout);
        deleteRows(enclave_id, (int*)&status, delTestName, condition1, low, high);printf("del5\n");fflush(stdout);
        deleteRows(enclave_id, (int*)&status, delTestName, condition1, low, high);printf("del6\n");fflush(stdout);
        indexSelect(enclave_id, (int*)&status, delTestName, -1, noCondition, -1, -1, -1, low, high);
    	//printf("selected! %d %d\n", low, high);
    	//printTable(enclave_id, (int*)&status, "ReturnTable");
*/

    	/*createTestTableIndex(enclave_id, (int*)&status, "testTable", 10);
    	saveIndexTable(enclave_id, (int*)&status, "testTable", 10);
    	deleteTable(enclave_id, (int*)&status, "testTable");
    	createTestTableIndex(enclave_id, (int*)&status, "testTable", 50);
    	saveIndexTable(enclave_id, (int*)&status, "testTable", 50);
    	deleteTable(enclave_id, (int*)&status, "testTable");
    	createTestTableIndex(enclave_id, (int*)&status, "testTable", 100);
    	saveIndexTable(enclave_id, (int*)&status, "testTable", 100);
    	deleteTable(enclave_id, (int*)&status, "testTable100");*/

    	/*createTestTableIndex(enclave_id, (int*)&status, "testTable", 50);
    	saveIndexTable(enclave_id, (int*)&status, "testTable", 50);
    	deleteTable(enclave_id, (int*)&status, "testTable");
    	loadIndexTable(enclave_id, (int*)&status, 50);
    	printf("loaded!\n");fflush(stdout);
        indexSelect(enclave_id, (int*)&status, "testTable50", -1, condition1, -1, -1, -1, low, high);
    	printf("selected!\n");
    	printTable(enclave_id, (int*)&status, "ReturnTable");*/
/*
    	createTestTableIndex(enclave_id, (int*)&status, "testTable", 500);
    	saveIndexTable(enclave_id, (int*)&status, "testTable", 500);
    	deleteTable(enclave_id, (int*)&status, "testTable");
    	createTestTableIndex(enclave_id, (int*)&status, "testTable", 1000);
    	saveIndexTable(enclave_id, (int*)&status, "testTable", 1000);
    	deleteTable(enclave_id, (int*)&status, "testTable");
    	createTestTableIndex(enclave_id, (int*)&status, "testTable", 5000);
    	saveIndexTable(enclave_id, (int*)&status, "testTable", 5000);
    	deleteTable(enclave_id, (int*)&status, "testTable");
    	createTestTableIndex(enclave_id, (int*)&status, "testTable", 10000);
    	saveIndexTable(enclave_id, (int*)&status, "testTable", 10000);
    	deleteTable(enclave_id, (int*)&status, "testTable");
    	createTestTableIndex(enclave_id, (int*)&status, "testTable", 50000);
    	saveIndexTable(enclave_id, (int*)&status, "testTable", 50000);
    	deleteTable(enclave_id, (int*)&status, "testTable");
    	createTestTableIndex(enclave_id, (int*)&status, "testTable", 100000);
    	saveIndexTable(enclave_id, (int*)&status, "testTable", 100000);
    	deleteTable(enclave_id, (int*)&status, "testTable");
    	createTestTableIndex(enclave_id, (int*)&status, "testTable", 500000);
    	saveIndexTable(enclave_id, (int*)&status, "testTable", 500000);
    	deleteTable(enclave_id, (int*)&status, "testTable");
    	createTestTableIndex(enclave_id, (int*)&status, "testTable", 1000000);
    	saveIndexTable(enclave_id, (int*)&status, "testTable", 1000000);
    	deleteTable(enclave_id, (int*)&status, "testTable");*/
    	//loadIndexTable(enclave_id, (int*)&status, "testTable");
    	//printf("loaded!\n");fflush(stdout);
        //indexSelect(enclave_id, (int*)&status, "testTable", -1, condition1, -1, -1, -1, low, high);
    	//printf("selected!\n");
    	//printTable(enclave_id, (int*)&status, "ReturnTable");


        //ret = newStructure(enclave_id, TYPE_TREE_ORAM, (*oramCapacity*2-1)*BUCKET_SIZE); //real size of oram is bigger than logical size
        //JK, ignore all this, I'm going to call the testing ecall. TODO: clean this and the service_provider up later
        //ret = newStructure(enclave_id, TYPE_LINEAR_SCAN, 7);//as per the requirements of the hard-coded test
        /*run_tests(enclave_id, &status);
        if(ret || status != SGX_SUCCESS){
        	printf("operation failed.\n");
        	goto CLEANUP;
        }*/


        //testMemory(enclave_id, &status);

        //begin performance tests for data structures

        //int numQueries = 50;
        //int numBlocks = pow(2, NUM_BLOCKS_POW)-1;
        //for(int n = 5; n < 6; n++){//make this something like 150 later and run for many different data block sizes
        	//numBlocks = pow(2, n)-1;
            //set up encrypted linear scan

        /*switch(TEST_TYPE){
        case 1:
        {
            printf("setting up encrypted linear scan\n");
            setupPerformanceTest(enclave_id, &status, 0, numBlocks, TYPE_LINEAR_SCAN);
            if(ret || status != SGX_SUCCESS){
            	printf("setting up encrypted linear scan failed.\n");
            	goto CLEANUP;
            }
            Linear_Scan_Block* b1 = (Linear_Scan_Block*)malloc(sizeof(Linear_Scan_Block));
            //run encrypted linear scan
            //printf("running encrypted linear scan\n");
            time_t startEnc = clock();
            for(int i = 0; i < numQueries; i++) {//printf("here");fflush(stdout);
                testLinScanBlockPerformance(enclave_id, &status, 0, numBlocks/2, b1, sizeof(Linear_Scan_Block));
            }
            time_t endEnc = clock();
            double elapsedEnc = (double)(endEnc - startEnc)/(CLOCKS_PER_SEC);
            if(ret || status != SGX_SUCCESS){
            	printf("encrypted linear scan failed.\n");
            	goto CLEANUP;
            }
            printf("Linear_Encrypted| numBlocks: %d, BLOCK_DATA_SIZE: %d, numQueries: %d, time: %f\n", numBlocks, BLOCK_DATA_SIZE, numQueries, elapsedEnc);
            //free the memory we used
            free(oblivStructures[0]);
            free(b1);
        }
        	break;
        case 2:
        {
            //set up unencrypted linear scan
            printf("setting up unencrypted linear scan\n");
            setupPerformanceTest(enclave_id, &status, 0, numBlocks, TYPE_LINEAR_UNENCRYPTED);
            if(ret || status != SGX_SUCCESS){
            	printf("setting up unencrypted linear scan failed.\n");
            	goto CLEANUP;
            }
            Linear_Scan_Block* b2 = (Linear_Scan_Block*)malloc(sizeof(Linear_Scan_Block));
            //run unencrypted linear scan
            //printf("running unencrypted linear scan\n");
            time_t startUnEnc = clock();
            for(int i = 0; i < numQueries; i++) {
                testLinScanBlockUnencryptedPerformance(enclave_id, &status, 0, numBlocks/2, b2, sizeof(Linear_Scan_Block));
            }
            time_t endUnEnc = clock();
            double elapsedUnEnc = (double)(endUnEnc - startUnEnc)/(CLOCKS_PER_SEC);
            if(ret || status != SGX_SUCCESS){
            	printf("unencrypted linear scan failed.\n");
            	goto CLEANUP;
            }
            printf("Linear_Unencrypted| numBlocks: %d, BLOCK_DATA_SIZE: %d, numQueries: %d, time: %f\n", numBlocks, BLOCK_DATA_SIZE, numQueries, elapsedUnEnc);
            //free the memory we used
            free(oblivStructures[0]);
            free(b2);
        }
        	break;
        case 3:
        {
            //set up oram
            //printf("setting up oram\n");
            setupPerformanceTest(enclave_id, &status, 0, numBlocks, TYPE_ORAM);
            if(ret || status != SGX_SUCCESS){
            	printf("setting up oram failed.\n");
            	goto CLEANUP;
            }
            Oram_Block* b3 = (Oram_Block*)malloc(sizeof(Oram_Block));
            //initialize all the blocks so we get a realistic test
            for(int i = 0; i < numBlocks; i++){
            	testOramPerformance(enclave_id, &status, 0, i, b3, sizeof(Oram_Block));
            }
            //run oram
            //printf("running oram\n");
            time_t startOram = clock();
            for(int i = 0; i < numQueries; i++) {
                testOramPerformance(enclave_id, &status, 0, numBlocks/2, b3, sizeof(Oram_Block));
            }
            time_t endOram = clock();
            double elapsedOram = (double)(endOram - startOram)/(CLOCKS_PER_SEC);
            if(ret || status != SGX_SUCCESS){
            	printf("oram failed.\n");
            	goto CLEANUP;
            }
            printf("ORAM| numBlocks: %d, BLOCK_DATA_SIZE: %d, numQueries: %d, time: %f\n", numBlocks, BLOCK_DATA_SIZE, numQueries, elapsedOram);
            //free the memory we used
            //function to free the memory used for the position map
            free_oram(enclave_id, &status, 0);
            free(oblivStructures[0]);
            free(b3);
        }
        	break;
        case 4:
        {
            //set up "safe" oram
            printf("setting up safe oram\n");
            setupPerformanceTest(enclave_id, &status, 0, numBlocks, TYPE_ORAM);
            if(ret || status != SGX_SUCCESS){
            	printf("setting up oram failed.\n");
            	goto CLEANUP;
            }
            Oram_Block* b3 = (Oram_Block*)malloc(sizeof(Oram_Block));
            //initialize all the blocks so we get a realistic test
            for(int i = 0; i < numBlocks; i++){
            	testOramPerformance(enclave_id, &status, 0, i, b3, sizeof(Oram_Block));
            }
            //run oram
            //printf("running oram\n");

            //temp for distribuction experiment
            oramDistribution(enclave_id, &status, 0);

            break;
            //end temp
            time_t startOram = clock();
            for(int i = 0; i < numQueries; i++) {
                testOramSafePerformance(enclave_id, &status, 0, numBlocks/2, b3, sizeof(Oram_Block));
            }
            time_t endOram = clock();
            double elapsedOram = (double)(endOram - startOram)/(CLOCKS_PER_SEC);
            if(ret || status != SGX_SUCCESS){
            	printf("oram failed.\n");
            	goto CLEANUP;
            }
            printf("ORAMSafe| numBlocks: %d, BLOCK_DATA_SIZE: %d, numQueries: %d, time: %f\n", numBlocks, BLOCK_DATA_SIZE, numQueries, elapsedOram);
            //free the memory we used
            //function to free the memory used for the position map
            free_oram(enclave_id, &status, 0);
            free(oblivStructures[0]);
            free(b3);
        }
        	break;
        case 5:
        {
            printf("setting up encrypted linear scan write\n");
            setupPerformanceTest(enclave_id, &status, 0, numBlocks, TYPE_LINEAR_SCAN);
            if(ret || status != SGX_SUCCESS){
            	printf("setting up encrypted linear scan write failed.\n");
            	goto CLEANUP;
            }
            Linear_Scan_Block* b1 = (Linear_Scan_Block*)malloc(sizeof(Linear_Scan_Block));
            //run encrypted linear scan
            //printf("running encrypted linear scan\n");
            time_t startEnc = clock();
            for(int i = 0; i < numQueries; i++) {//printf("here");fflush(stdout);
                testLinScanBlockWritePerformance(enclave_id, &status, 0, numBlocks/2, b1, sizeof(Linear_Scan_Block));
            }
            time_t endEnc = clock();
            double elapsedEnc = (double)(endEnc - startEnc)/(CLOCKS_PER_SEC);
            if(ret || status != SGX_SUCCESS){
            	printf("encrypted linear scan failed.\n");
            	goto CLEANUP;
            }
            printf("Linear_EncryptedWrite| numBlocks: %d, BLOCK_DATA_SIZE: %d, numQueries: %d, time: %f\n", numBlocks, BLOCK_DATA_SIZE, numQueries, elapsedEnc);
            //free the memory we used
            free(oblivStructures[0]);
            free(b1);
        	break;
        }
        case 6:
        {
            //set up unencrypted linear scan
            printf("setting up unencrypted linear scan write\n");
            setupPerformanceTest(enclave_id, &status, 0, numBlocks, TYPE_LINEAR_UNENCRYPTED);
            if(ret || status != SGX_SUCCESS){
            	printf("setting up unencrypted linear scan write failed.\n");
            	goto CLEANUP;
            }
            Linear_Scan_Block* b2 = (Linear_Scan_Block*)malloc(sizeof(Linear_Scan_Block));
            //run unencrypted linear scan
            //printf("running unencrypted linear scan\n");
            time_t startUnEnc = clock();
            for(int i = 0; i < numQueries; i++) {
                testLinScanBlockUnencryptedWritePerformance(enclave_id, &status, 0, numBlocks/2, b2, sizeof(Linear_Scan_Block));
            }
            time_t endUnEnc = clock();
            double elapsedUnEnc = (double)(endUnEnc - startUnEnc)/(CLOCKS_PER_SEC);
            if(ret || status != SGX_SUCCESS){
            	printf("unencrypted linear scan failed.\n");
            	goto CLEANUP;
            }
            printf("Linear_UnencryptedWrite| numBlocks: %d, BLOCK_DATA_SIZE: %d, numQueries: %d, time: %f\n", numBlocks, BLOCK_DATA_SIZE, numQueries, elapsedUnEnc);
            //free the memory we used
            free(oblivStructures[0]);
            free(b2);
        }
        	break;
        default:
        	printf("invalid TEST_TYPE!\n");
        	break;
        }*/
        //}

        /*testOpOram(enclave_id, &status);
        if(ret || status != SGX_SUCCESS){
        	printf("oram correctness test failed.\n");
        	goto CLEANUP;
        }*/

    }
    /*
     *
     *
     *End Saba's Code
     *
     *
	*/

CLEANUP:
    // Clean-up
    // Need to close the RA key state.
    if(INT_MAX != context)
    {
        int ret_save = ret;
        ret = enclave_ra_close(enclave_id, &status, context);
        if(SGX_SUCCESS != ret || status)
        {
            ret = -1;
            fprintf(OUTPUT, "\nError, call enclave_ra_close fail [%s].",
                    __FUNCTION__);
        }
        else
        {
            // enclave_ra_close was successful, let's restore the value that
            // led us to this point in the code.
            ret = ret_save;
        }
        fprintf(OUTPUT, "\nCall enclave_ra_close success.\n");
    }

    sgx_destroy_enclave(enclave_id);

	CloseDB();

    //todo(Saba): need to free stuff that I used in the code I added
    /*moved up
     * ra_free_network_response_buffer(p_msg0_resp_full);
    ra_free_network_response_buffer(p_msg2_full);
    ra_free_network_response_buffer(p_att_result_msg_full);

    // p_msg3 is malloc'd by the untrusted KE library. App needs to free.
    SAFE_FREE(p_msg3);
    SAFE_FREE(p_msg3_full);
    SAFE_FREE(p_msg1_full);
    SAFE_FREE(p_msg0_full);*/
    //printf("\nEnter a character before exit ...\n");
    //getchar();
    return ret;
}

