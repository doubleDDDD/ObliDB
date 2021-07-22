#pragma once

#include <sys/stat.h>
#include <cxxabi.h>
#include <list>
#include <atomic>
#include <cstring>
#include <iostream>
#include <fstream>
#include <map>
#include <vector>
#include <memory>
#include <string>
#include <cstdlib>
#include <unordered_map>
#include <condition_variable>
#include <mutex>
#include <climits>

#include "../isv_enclave/definitions.h"//structs, enums, fixed constants

// #define PERSIST_ENGINE
// #define VALUME_ATTACK
namespace oblidbextraio {
/***********************/

#define PAGE_SIZE 4096  // same with filesystem IO
#define BUFFER_POOL_SIZE 32
#define EXTRA_BUCKET_SIZE 8
#define INVALID_PAGE_ID -1
#define HEADER_PAGE_ID 0

typedef int64_t page_id_t;

class RWMutex;

template <typename K, typename V> 
class HashTable;

template <typename K, typename V> 
class ExtendibleHash;

template <typename T> 
class Replacer;

template <typename T> 
class LRUReplacer;

class Page;
class DiskManager;
class BufferPoolManager;
class StorageEngine;

class TablePage;

static char *buffer_used = nullptr;

/**
 * 读写锁
*/
class RWMutex {
    typedef std::mutex mutex_t;
    // The condition_variable class is a synchronization primitive that can be used 
    // to block a thread, or multiple threads at the same time
    // until another thread both modifies a shared variable (the condition), and notifies the condition_variable
    // 即线程阻塞在某个条件变量上
    typedef std::condition_variable cond_t;
    static const uint32_t max_readers_ = UINT_MAX;

public:
    RWMutex() : reader_count_(0), writer_entered_(false) {}

    ~RWMutex() {
        /**
         * @brief 
         *  When a lock_guard object is created
         *  it attempts to take ownership of the mutex it is given
         *  When control leaves the scope in which the lock_guard object was created
         *  the lock_guard is destructed and the mutex is released.
         * @return std::lock_guard<mutex_t> @c 
         */
        std::lock_guard<mutex_t> guard(mutex_);  /* 持有锁 */

        /* 运行结束之后会自动释放锁 */
    }

    // disable copy 构造函数
    RWMutex(const RWMutex &) = delete;
    RWMutex &operator=(const RWMutex &) = delete;

    void WLock() {
        /* 构造一个 unique_lock 对象 lock,  */
        std::unique_lock<mutex_t> lock(mutex_);  /* 还未持有锁，继续执行 */
        /**
         * @brief after the wait, we own the lock
         */
        while (writer_entered_)
            reader_.wait(lock);  /* 如果有其它写者的话 先挂在 reader上 */
        writer_entered_ = true;  /* 安全的修改了 writer_entered_ 表明有写者想要入场 */
        /* 如果始终有读者，则写者始终等待 */
        while (reader_count_ > 0)
            writer_.wait(lock);

        /* 写者等待完成，得到了锁，开始执行临界区代码 */
    }

    void WUnlock() {
        /* 本身该函数的执行有一个原子的语义 */
        std::lock_guard<mutex_t> guard(mutex_);  /* 得到锁 */
        writer_entered_ = false;  /* 写完了 */
        reader_.notify_all();  /* 通知所有在 reader 上等待的线程，reader.wait()被唤醒 */
        /* 函数结束释放锁 */
    }

    void RLock() {
        std::unique_lock<mutex_t> lock(mutex_);  /* 还未持有锁 */
        /* 如果当前 有写者 或 读者数量 达到了最大，则读失败，当前线程被挂到reader上，直到被唤醒 */
        while (writer_entered_ || reader_count_ == max_readers_)
            reader_.wait(lock);
        // 被唤醒后，当前线程持有持有锁
        // 并且在读线程读的过程中，其它读者依然可以获取到读锁
        reader_count_++;
    }

    void RUnlock() {
        std::lock_guard<mutex_t> guard(mutex_);  /* 持有锁，该锁可重入 */
        reader_count_--;  /* 读者数量-1 */
        if (writer_entered_) {
            /* 如果有写者，且无读者，则优先唤醒 waiter 上的写者，写者每次只能有一个入场 */
            if (reader_count_ == 0)
                writer_.notify_one();
            /* 依然有读者，则写者等待 */
        } else {
            /* 如果没有写者，则唤醒一个等待队列上的读者，控制读者的数量 */
            if (reader_count_ == max_readers_ - 1)
                reader_.notify_one();
        }
        /* 离开之后释放锁 */
    }

private:
    mutex_t mutex_;  // 互斥体
    cond_t writer_;  // 线程可以阻塞在条件变量上
    cond_t reader_;
    uint32_t reader_count_;
    bool writer_entered_;
};

/**
 * LRU
*/
template <typename T> 
class Replacer {
public:
    Replacer() {}
    virtual ~Replacer() {}
    virtual void Insert(const T &value) = 0;
    virtual bool Victim(T &value) = 0;
    virtual size_t Size() const = 0;
};

template <typename T> 
class LRUReplacer : public Replacer<T> {
    struct node {
        node() = default;
        explicit node(T d, node *p = nullptr) : data(d), pre(p) {}
        T data;
        node *pre = nullptr;
        node *next = nullptr;
    };
public:
    // do not change public interface
    LRUReplacer() : size_(0) {
        head_ = new node;
        tail_ = head_;
    }

    ~LRUReplacer()  = default;

    // disable copy
    LRUReplacer(const LRUReplacer &) = delete;
    LRUReplacer &operator=(const LRUReplacer &) = delete;

    /* access 之后所触发的 insert */
    void Insert(const T &value) {
        std::lock_guard<std::mutex> lock(mutex_);

        auto it = table_.find(value);
        if(it == table_.end()) {
            tail_->next = new node(value, tail_);
            tail_ = tail_->next;
            table_.emplace(value, tail_);  // 用来替代push_back的
            ++size_;
        } else {
            // 该页面是新插入的，如果本来就在队列尾就不用重新操作指针了
            if(it->second != tail_) {
                // 先从原位置移除
                node *pre = it->second->pre;
                node *cur = pre->next;
                pre->next = std::move(cur->next);
                pre->next->pre = pre;

                // 再放到尾部
                cur->pre = tail_;
                tail_->next = std::move(cur);
                tail_ = tail_->next;
            }
        }
    }

    /* 对 page 操作的过程中是拿下来的 */
    bool Erase(const T &value) {
        std::lock_guard<std::mutex> lock(mutex_);

        auto it = table_.find(value);
        if(it != table_.end()) {
            /* exist */
            if(it->second != tail_) {
                /* 不在队首，拿下来的时候需要其它操作 */
                node *pre = it->second->pre;
                node *cur = pre->next;
                pre->next = std::move(cur->next);
                pre->next->pre = pre;
            } else {
                /* 直接拿走 */
                tail_ = tail_->pre;
                delete tail_->next;
            }

            table_.erase(value);
            if(--size_ == 0) {
                tail_ = head_;
            }
            return true;
        }

        return false;
    }

    /* 满了之后的替换策略，将一个page写下去 */
    bool Victim(T &value) {
        std::lock_guard<std::mutex> lock(mutex_);

        if(size_ == 0) {
            return false;
        }

        value = head_->next->data;
        head_->next = head_->next->next;
        if(head_->next != nullptr) {
            head_->next->pre = head_;
        }

        table_.erase(value);
        if(--size_ == 0) {
            tail_ = head_;
        }

        return true;
    }

    /* 仅仅做记录，大小不限制 */
    size_t Size() const {
        std::lock_guard<std::mutex> lock(mutex_);
        return size_;
    }
private:
    mutable std::mutex mutex_;
    size_t size_;
    std::unordered_map<T, node *> table_;  /* 底层实现是hash表，无序的kv */
    node *head_;
    node *tail_;
};

/**
 * extend hash table
*/
template <typename K, typename V> 
class HashTable {
public: 
    HashTable() {}
    virtual ~HashTable() {}
    virtual bool Find(const K &key, V &value) = 0;
    virtual bool Remove(const K &key) = 0;
    virtual void Insert(const K &key, const V &value) = 0;
    virtual size_t Size() const = 0;
};

/**
 * vector 存 bucket
 * bucket存kv map
 * 这里的 kv 是 page_id 与 page*
 * 可扩展的动态hash
 */
template <typename K, typename V>
class ExtendibleHash : public HashTable<K, V> {
    struct Bucket {
        /* = default 在写了带参数的构造函数之后依然需要一个默认构造函数 */
        Bucket() = default;
        /* explicit防止类型转换的构造函数 */
        explicit Bucket(size_t i, int d) : id(i), depth(d) {}
        std::map<K, V> items; // key-value pairs
        size_t id = 0;                 // id of Bucket
        int depth = 0;                 // local depth counter
    };
public:
    ExtendibleHash(size_t size) : bucket_size_(size), bucket_count_(0), pair_count_(0), depth(0){
        bucket_.emplace_back(new Bucket(0, 0));  /* 初始化一个新桶 */
        bucket_count_ = 1;
    }

    size_t HashKey(const K &key) {return std::hash<K>()(key);}

    // 查找桶里的哈希表是否有该值
    bool Find(const K &key, V &value){
        std::lock_guard<std::mutex> lock(mutex_);

        size_t position = HashKey(key) & ((1 << depth) - 1);

        if(bucket_[position]) {
            if(bucket_[position]->items.find(key) != bucket_[position]->items.end()) {
                value = bucket_[position]->items[key];
                return true;
            }
        }
        return false;
    }

    // 插入元素
    void Insert(const K &key, const V &value) {
        std::lock_guard<std::mutex> lock(mutex_);

        size_t bucket_id = HashKey(key) & ((1 << depth) - 1);
        // 找到插入的位置，如果为空则新建一个桶
        if(bucket_[bucket_id] == nullptr) {
            bucket_[bucket_id] = std::make_shared<Bucket>(bucket_id, depth);
            ++bucket_count_;
        }

        /* 无论是新建的还是之前就有的，反正是得到了一个桶 */
        auto bucket = bucket_[bucket_id];

        // update
        if(bucket->items.find(key) != bucket->items.end()) {
            bucket->items[key] = value;
            return;
        }

        // 插入键值对
        bucket->items.insert({key, value});
        ++pair_count_;

        if(bucket->items.size() > bucket_size_){
            auto old_index = bucket->id;
            auto old_depth = bucket->depth;

            std::shared_ptr<Bucket> new_bucket = split(bucket);  /* 分裂新桶一个出来 */

            // 溢出了就改回原来的深度
            if(new_bucket == nullptr) {
                bucket->depth = old_depth;
                return;
            }
            // 若插入的桶的局部深度大于全局深度，则要扩展桶数组
            if(bucket->depth > depth) {
                auto size = bucket_.size();
                // 超出一个之后就开始补了，所以是扩展2倍
                auto factor = (1 << (bucket->depth - depth));

                depth = bucket->depth;
                // resize函数重新分配大小，改变容器的大小，并且创建对象 就是rehash的过程
                bucket_.resize(bucket_.size() * factor);

                bucket_[bucket->id] = bucket;
                bucket_[new_bucket->id] = new_bucket;

                // 遍历桶数组，已经重新分配过大小了
                for(size_t i = 0; i < size; ++i) {
                    if(bucket_[i]) {
                        if(i < bucket_[i]->id){
                            bucket_[i].reset();  // 释放当前的对象
                        } else {
                            auto step = 1 << bucket_[i]->depth;
                            for(size_t j = i + step; j < bucket_.size(); j += step) {
                                bucket_[j] = bucket_[i];
                            }
                        }
                    }
                }
            } else {
                /* 只是增加一个新桶的话就还算比较简单 */
                for (size_t i = old_index; i < bucket_.size(); i += (1 << old_depth)) {
                    bucket_[i].reset();
                }

                bucket_[bucket->id] = bucket;
                bucket_[new_bucket->id] = new_bucket;

                auto step = 1 << bucket->depth;
                for (size_t i = bucket->id + step; i < bucket_.size(); i += step) {
                    bucket_[i] = bucket;
                }
                for (size_t i = new_bucket->id + step; i < bucket_.size(); i += step) {
                    bucket_[i] = new_bucket;
                }
            }
        }
    }

    // 移除元素
    bool Remove(const K &key){
        std::lock_guard<std::mutex> lock(mutex_);

        size_t position = HashKey(key) & ((1 << depth) - 1);
        size_t cnt = 0;
        if(bucket_[position]) {
            auto tmp_bucket = bucket_[position];
            cnt = tmp_bucket->items.erase(key);
            pair_count_ -= cnt;
        }
        return cnt != 0;
    }

    size_t Size() const { 
        std::lock_guard<std::mutex> lock(mutex_);
        return pair_count_; 
    }

    // 返回哈希表当前深度
    int GetGlobalDepth() const {
        std::lock_guard<std::mutex> lock(mutex_);
        return depth;
    }

    // 返回给定偏移的局部深度
    int GetLocalDepth(int bucket_id) const {
        std::lock_guard<std::mutex> lock(mutex_);

        if(bucket_[bucket_id]) {
            return bucket_[bucket_id]->depth;
        }
        return -1;
    }

    // 返回桶总数
    int GetNumBuckets() const {
        std::lock_guard<std::mutex> lock(mutex_);
        return bucket_count_;
    }  

private:
    mutable std::mutex mutex_;
    const size_t bucket_size_;
    int bucket_count_;
    size_t pair_count_;
    int depth;
    std::vector<std::shared_ptr<Bucket>> bucket_;    // 桶数组

    std::shared_ptr<Bucket> split(std::shared_ptr<Bucket> &b) {
        auto res = std::make_shared<Bucket>(0, b->depth);
        while(res->items.empty()){
            b->depth++;
            res->depth++;

            for(auto it=b->items.begin(); it!=b->items.end();) {
                if (HashKey(it->first) & (1 << (b->depth - 1))){
                    res->items.insert(*it);  // 新桶中插入
                    res->id = HashKey(it->first) & ((1 << b->depth) - 1);
                    it = b->items.erase(it);
                } else {
                    ++it;  // 保留在原桶中的pair
                }
            }

            if(b->items.empty()) {
                b->items.swap(res->items);
                b->id = res->id;
            }
        }

        ++bucket_count_;
        return res;
    }
};

/**
 * 内存中的基本存储单元是page
 */
class Page {
    friend class BufferPoolManager;
public:
    Page() { ResetMemory(); }
    ~Page() {};

    /**
     * disable copy
     * 禁止copy构造函数
     * 禁止=操作符
     */
    Page(Page const &) = delete;
    Page &operator=(Page const &) = delete;

    // get actual data page content
    inline char *GetData() { return data_; }
    
    // get page id
    inline page_id_t GetPageId() { return page_id_; }

    // method use to latch/unlatch page content
    inline void WLatch() { rwlatch_.WLock(); }  /* 加写锁 */
    inline void WUnlatch() { rwlatch_.WUnlock(); }  /* 写完成 */
    inline void RLatch() { rwlatch_.RLock(); }  /* 加读锁 */
    inline void RUnlatch() { rwlatch_.RUnlock(); }  /* 读完成 */
private:
    inline void ResetMemory() { memset(data_, 0, PAGE_SIZE); }
    char data_[PAGE_SIZE];
    page_id_t page_id_ = INVALID_PAGE_ID;  /* 表示page跟踪的物理页面 */

    /* 如果有工作线程要access这个page，则需要先pin再unpin */
    int pin_count_ = 0;
    bool is_dirty_ = false;
    RWMutex rwlatch_;  // 读写锁
};

/**
 * Database use the first page (page_id = 0) as header page to store metadata, in
 * our case, we will contain information about table/index name (length less than
 * 32 bytes, max is 31 bytes) and their corresponding root_id
 *
 * Format (size in byte):
 * 增加一些table的元数据，在本例中
 *      加密块大小
 *      table 的 tuple数量
 *      类型
 * 都需要持久化记录
 * schema 持久化 here, 这么搞一个page放不下几张表的感觉
 * length of one record
 *  32 + 4 + 4 + 4 + 4 + 4 + n*12
 *     52 + n*12 
 *  -----------------------------------------------------------------
 * | RecordCount (4) | curoffset (4) | key valid flag (4) | keylen (4) | secret key (32 bytes) | Entry_1 name (32) | Entry_1 root_id (4) | Entry_1 EncBlockSize (4) | Entry_1 row_num (4) | Entry_1 type(4) |
 * | numFields (4) | first fieldOffsets(4) | first fieldSizes(4) | first fieldTypes(4) | second fieldOffsets | second fieldSizes | second fieldTypes | ... |
 *  -----------------------------------------------------------------
 */
#define HEADHEAD 4
#define ONE_RECORD_FIX_LEN 52
#define ONE_RECORD_VARIABLE 12
#define TABLE_NAME_LEN_MAX 32
#define KEY_VALID_FLAG 4  // 4 字节的有效位
#define KEY_LEN_FLAG 4  // 4 字节去表示 sgx 秘钥的长度
#define KEY_LEN_MAX 32  // sgx 秘钥最大 32 字节
#define BEGIN_OFFSET 2*HEADHEAD + KEY_VALID_FLAG + KEY_LEN_FLAG + KEY_LEN_MAX
class HeaderPage : public Page {
public:
    void Init() { 
        /* page 创建时被调用，仅一次 */
        SetRecordCount(0); 
        SetResordOffset(BEGIN_OFFSET);
        SetKeyValidFlag(false);
    }

    /* Record related */
    bool InsertRecord(
        const std::string &name,
        Schema* schema, 
        const page_id_t root_id,
        int encBlockSize,
        int rownum,
        int type
    )
    {
        // printf("root page id: %d\n", root_id);
        assert(root_id>0);
        assert(name.length() < TABLE_NAME_LEN_MAX);
        assert(root_id > INVALID_PAGE_ID);

        int numfileds = schema->numFields;
        int rnum = GetRecordCount();
        int offset = GetOffset();

        /* check if offset is too large */
        if (PAGE_SIZE - offset < ONE_RECORD_FIX_LEN + numfileds*ONE_RECORD_VARIABLE) { 
            return false; 
        }

        /* 检查重名 */
        if (FindRecord(name) != -1) { return false; }

        // copy record content
        memcpy(GetData() + offset, name.c_str(), (name.length() + 1));
        memcpy((GetData() + offset + 32), &root_id, 4);
        memcpy((GetData() + offset + 36), &encBlockSize, 4);
        memcpy((GetData() + offset + 40), &rownum, 4);
        memcpy((GetData() + offset + 44), &type, 4);
        memcpy((GetData() + offset + 48), &numfileds, 4);

        for(int i=0;i<numfileds;++i){
            memcpy((GetData() + offset + 52 + i*12 + 0), &(schema->fieldOffsets[i]), 4);
            memcpy((GetData() + offset + 52 + i*12 + 4), &(schema->fieldSizes[i]), 4);
            memcpy((GetData() + offset + 52 + i*12 + 8), &(schema->fieldTypes[i]), 4);
        }

        SetRecordCount(rnum + 1);
        SetResordOffset(offset + ONE_RECORD_FIX_LEN + numfileds*ONE_RECORD_VARIABLE);

        return true;
    }

    // bool DeleteRecord(const std::string &name){
    //     int rnum = GetRecordCount();
    //     assert(rnum > 0);

    //     int index = FindRecord(name);
    //     if(index == -1) {return false;}

    //     int offset = 4 + index * 36;
    //     /* 整体前移 */
    //     memmove(GetData() + offset, GetData() + offset + 36, (rnum - index - 1) * 36);
    //     SetRecordCount(rnum - 1);
    //     return true;
    // };

    // bool UpdateRecord(const std::string &name, const page_id_t root_id){
    //     assert(name.length() < 32);

    //     int index = FindRecord(name);
    //     if(index == -1) {return false;}

    //     int offset = 4 + index * 36;
    //     memcpy((GetData() + offset + 32), &root_id, 4);

    //     return true;
    // }

    // return root_id if success
    bool GetRootId(const std::string &name, page_id_t &root_id) 
    {
        assert(name.length() < TABLE_NAME_LEN_MAX);

        int offset = FindRecord(name);
        if(offset == -1) { return false; }

        /**
         * 0: 4 + 32:           36
         * 1: 4 + 36 + 32:      36*2
         * 2: 4 + 36 + 36 + 32  36*3
         * deprecated
         */
        // int offset = (index + 1) * 36;
        offset += TABLE_NAME_LEN_MAX;
        root_id = *reinterpret_cast<page_id_t *>(GetData() + offset);
        return true;
    }

    /* helper functions */
    int FindRecord(const std::string &name)
    {
        int i;
        size_t rnum = GetRecordCount();

        int cursor = BEGIN_OFFSET;
        int curnumFields;

        for(i=0; i<rnum; ++i){
            char *raw_name = reinterpret_cast<char *>(GetData()+cursor);
            if(strcmp(raw_name, name.c_str())==0) {return cursor;}
            curnumFields = *reinterpret_cast<int *>(GetData() + cursor + 48);
            cursor += curnumFields*ONE_RECORD_VARIABLE + ONE_RECORD_FIX_LEN;
        }
        return -1;
    }

    int GetRecordOffset(int index)
    {
        int i;
        size_t rnum = GetRecordCount();
        int cursor = BEGIN_OFFSET;
        int curnumFields;

        for(i=0; i<rnum; ++i){
            if(i==index) { return cursor; }
            curnumFields = *reinterpret_cast<int *>(GetData() + cursor + 48);
            cursor += curnumFields*ONE_RECORD_VARIABLE + ONE_RECORD_FIX_LEN;
        }
        return -1;
    }

    int GetRecordCount(){
        return *reinterpret_cast<int *>(GetData());
    }

    int GetOffset() {
        return *reinterpret_cast<int *>(GetData() + HEADHEAD);
    }

    bool ValidKey(){
        int v = *reinterpret_cast<int *>(GetData() + 2*HEADHEAD);
        return static_cast<bool>(v);
    }

    void GetKey(unsigned char* lkey){
        // int keylen = *reinterpret_cast<int *>(GetData() + 3*HEADHEAD);
        for(int y=0;y<16;++y){
            lkey[y] = \
                *reinterpret_cast<unsigned char*>(GetData() + 4*HEADHEAD + y);
        }
        // return reinterpret_cast<char *>(GetData() + 4*HEADHEAD);
    }

    void SetKeyValidFlag(bool v){
        // int vv = static_cast<int>(vv);
        // printf("value is %d\n", v);
        memcpy(GetData() + 2*HEADHEAD, &v, 4);
    }

    // only set once，在有效位无效时 set
    void SetKey(unsigned char* key, int keysize){
        /* debug */
        // for(int i=0;i<16;++i){
        //     printf("set %d %c\n", i, *(key+i));;
        // }
        assert(keysize<=KEY_LEN_MAX);
        memcpy(GetData() + 3*HEADHEAD ,&keysize, 4);
        memcpy(GetData() + 4*HEADHEAD, key, keysize);
    }

private:
    void SetRecordCount(int record_count){
        memcpy(GetData(), &record_count, 4);
    }

    void SetResordOffset(int offset){
        memcpy(GetData() + HEADHEAD, &offset, 4);
    }
};

/**
 * 封装一下 tuple, 实际上是完整的加密后的块
 */
class Tuple{
public:
    Tuple()=default;

    Tuple(int32_t _size, char* buffer):size(_size) {
        data = new char[size];
        memcpy((void *)data, (void *)buffer, size);
    }

    ~Tuple(){
        if(data){
            delete[] data;
            data = nullptr;
        }
    }

    void SetData(char* buffer, int32_t _size){
        data = new char[_size];
        size = _size;
        memcpy(data, buffer, size);
    }

    char* GetData() const { return data; }
    int32_t GetSize() const { return size; }

private:
    int32_t size;
    char* data;
};


#define PAGE_OFFSET  0
#define PREPAGE_OFFSET  12 
#define NEXTPAGE_OFFSET 20
#define FREE_POINTER_OFFSET 28
#define TUPLECOUNT_OFFSET 32
#define TUPLE_META_LEN 12
#define PAGE_ID_LEN 8
#define TUPLE_SLOT_OFFSET 36

/**
 * 字段修改为 8 位 in oblidb, 其实主要是 pageid 需要占 8 位
 * tuple page
 * header + slot
 *
 * Slotted page format:
 *  ---------------------------------------
 * | HEADER | ... FREE SPACES ... | TUPLES |
 *  ---------------------------------------
 *                                 ^
 *                         free space pointer 从后向前的
 *
 *  Header format (size in byte):
 *  --------------------------------------------------------------------------
 * | PageId (8)| LSN (4, 保留)| PrevPageId (8)| NextPageId (8)| FreeSpacePointer(4) |
 *  --------------------------------------------------------------------------
 *  --------------------------------------------------------------
 * | TupleCount (4) | Tuple_1 offset (4) | Tuple_1 size (4) | Tuple_1 index (4) | ... |
 *  --------------------------------------------------------------
 * 在一个 page 中，tuple slot 从前向后增长，空闲空间从后向前增长。FreeSpacePointer 在初始化的时候是指向 page 的尾端的
 * 一个 tuple 的 slot 占 8 个字节
 * size=0 意味着是一个 empty slot
 * 如果是线性扫描的 page 的话，没有必要这样复杂
 * 因为一个 table 的里表都是等长的，page header 记录一下它有多长，起始index是多少，有几个就足够了
 */
class TablePage : public Page {
public:
    /** 
     * 类内初始化，先于构造函数执行，会被构造函数覆盖
     * 构造函数无需再初始化它们了
     */
    /* Header related */
    void Init(page_id_t page_id, size_t page_size, page_id_t prev_page_id)
    {
        /* 按照上面的结构从前向后set */
        memcpy(GetData(), &page_id, 8);  /* set page id */
        SetPrevPageId(prev_page_id);
        SetNextPageId(INVALID_PAGE_ID);
        SetFreeSpacePointer(page_size);
        SetTupleCount(0);
    }

    page_id_t GetPageId() {
        return *reinterpret_cast<page_id_t *>(GetData()); 
    }

    page_id_t GetPrevPageId() { 
        return *reinterpret_cast<page_id_t *>(GetData() + PREPAGE_OFFSET); 
    }

    page_id_t GetNextPageId() { 
        return *reinterpret_cast<page_id_t *>(GetData() + NEXTPAGE_OFFSET); 
    }

    void SetPrevPageId(page_id_t prev_page_id) { 
        memcpy(GetData() + PREPAGE_OFFSET, &prev_page_id, PAGE_ID_LEN); 
    }

    void SetNextPageId(page_id_t next_page_id) {
        memcpy(GetData() + NEXTPAGE_OFFSET, &next_page_id, PAGE_ID_LEN); 
    }

    /**
    * Tuple related
    */
    bool InsertTuple(const Tuple &tuple, int index)
    {
        int dataSize = tuple.GetSize();
        // check if free space is enough
        if(dataSize > GetFreeSpaceSize()){
            return false;
        }

        // try to reuse a free slot first
        int i;
        for(i=0;i<GetTupleCount();++i){
            if(GetTupleSize(i)==0){break;}  // empty
        }

        // no free slot left, 没有空闲 slot，需要追加一个 slot 以及 数据本身
        // 一个 tuple 的元数据是 Tuple_1 offset (4), Tuple_1 size (4) 共计 8 字节
        if (i == GetTupleCount() && GetFreeSpaceSize() < tuple.GetSize() + TUPLE_META_LEN) {
            return false; // not enough space
        }

        // update free space pointer first
        SetFreeSpacePointer(GetFreeSpacePointer() - tuple.GetSize());
        // actually insert
        memcpy(GetData() + GetFreeSpacePointer(), tuple.GetData(), tuple.GetSize());
        // set metadata of tuple
        SetTupleOffset(i, GetFreeSpacePointer());
        SetTupleSize(i, tuple.GetSize());
        SetTupleIndex(i, index);

        if (i == GetTupleCount()) {
            // append a new slot and new data
            SetTupleCount(GetTupleCount() + 1);
        }

        return true;
    }

    /**
     * update tuple
     */
    bool UpdateTuple(const Tuple &tuple, int index)
    {
        int lastindex, firstindex, slotnr;

        lastindex = GetLastTupleIndex();
        if (index > lastindex) {
            return false;
        } else {
            firstindex = GetFirstTupleIndex();
            slotnr = index - firstindex;
            // printf("%d,%d,%d,%d\n", index, tuple.GetSize(), GetTupleSize(slotnr), slotnr);
            assert(tuple.GetSize() == GetTupleSize(slotnr));
            // just update is ok
            memcpy(GetData()+GetTupleOffset(slotnr), tuple.GetData(), tuple.GetSize());
            return true;
        }
    }

    bool GetTuple(Tuple &tuple, int index)
    {
        int lastindex, firstindex, slotnr;
        int tuplesize;
        int tupleoffset;
        lastindex = GetLastTupleIndex();

        if (index > lastindex) {
            return false;
        } else {
            firstindex = GetFirstTupleIndex();
            slotnr = index - firstindex;
            tuplesize = GetTupleSize(slotnr);
            tupleoffset = GetTupleOffset(slotnr);
            tuple.SetData((GetData()+tupleoffset), tuplesize);
            return true;
        }
    }
private:
    /**
    * helper functions
    */
    int32_t GetTupleOffset(int slot_num) { 
        return *reinterpret_cast<int32_t *>(GetData()  + TUPLE_SLOT_OFFSET + slot_num * TUPLE_META_LEN); 
    }

    int32_t GetTupleSize(int slot_num) { 
        return *reinterpret_cast<int32_t *>(GetData()  + TUPLE_SLOT_OFFSET + slot_num * TUPLE_META_LEN + 4); 
    }

    int32_t GetTupleIndex(int slot_num) { 
        return *reinterpret_cast<int32_t *>(GetData()  + TUPLE_SLOT_OFFSET + slot_num * TUPLE_META_LEN + 8); 
    }

    int32_t GetFirstTupleIndex() { return GetTupleIndex(0); }  /* 第一个 slot 中 tuple 对应的 index */

    int32_t GetLastTupleIndex(){
        int firstindex = GetFirstTupleIndex();
        int tuplecnt = GetTupleCount();
        return firstindex + tuplecnt - 1;
    }

    void SetTupleOffset(int slot_num, int32_t offset) { 
        memcpy(GetData() + TUPLE_SLOT_OFFSET + slot_num * TUPLE_META_LEN, &offset, 4); 
    }

    void SetTupleSize(int slot_num, int32_t size) { 
        memcpy(GetData() + TUPLE_SLOT_OFFSET + slot_num * TUPLE_META_LEN + 4, &size, 4); 
    }

    void SetTupleIndex(int slot_num, int32_t index) { 
        memcpy(GetData() + TUPLE_SLOT_OFFSET + slot_num * TUPLE_META_LEN + 8, &index, 4); 
    }

    // offset of the beginning of free space
    int32_t GetFreeSpacePointer() { 
        return *reinterpret_cast<int32_t *>(GetData()  + FREE_POINTER_OFFSET); 
    }

    void SetFreeSpacePointer(int32_t free_space_pointer) { 
        memcpy((GetData() + FREE_POINTER_OFFSET), &free_space_pointer, 4); 
    }

    // Note that this tuple count may be larger than # of
    int32_t GetTupleCount() { 
        return *reinterpret_cast<int32_t *>(GetData()  + TUPLECOUNT_OFFSET); 
    }

    // actual tuples because some slots may be empty
    void SetTupleCount(int32_t tuple_count) { 
        memcpy((GetData() + TUPLECOUNT_OFFSET), &tuple_count, 4); 
    }

    int32_t GetFreeSpaceSize() { 
        return GetFreeSpacePointer() - (TUPLE_SLOT_OFFSET + TUPLE_META_LEN * GetTupleCount()); 
    }

    friend void CheckTablePage(TablePage *);
};

inline void
CheckTablePage(TablePage *page)
{
    std::cout 
        << "Page id: " << page->GetPageId() << std::endl;
    std::cout 
        << "Prev id: " << page->GetPrevPageId() << std::endl;
    std::cout 
        << "Next id: " << page->GetNextPageId() << std::endl;
    std::cout 
        << "Free space pointer: " << page->GetFreeSpacePointer() << std::endl;
    std::cout 
        << "Tuple count: " << page->GetTupleCount() << std::endl;
    std::cout 
        << "Free space size: " << page->GetFreeSpaceSize() << std::endl;
    return;
}

/* 磁盘管理 */
class DiskManager {
public:
    DiskManager(const std::string &db_file) : file_name_(db_file), next_page_id_(0)
    {
        uint64_t pagesize;
        std::string::size_type n = file_name_.find(".");
        if (n == std::string::npos) {
            std::cerr << "wrong file format" << std::endl;
            return;
        }

        db_io_.open(db_file, std::ios::binary | std::ios::in | std::ios::out);  /* opendb文件 */
        // directory or file does not exist
        if (!db_io_.is_open()) {
            db_io_.clear();
            // create a new file
            db_io_.open(db_file, std::ios::binary | std::ios::trunc | std::ios::out);
            db_io_.close();
            // reopen with original mode
            db_io_.open(db_file, std::ios::binary | std::ios::in | std::ios::out);
        }

        // 计算文件大小
        pagesize = GetFileSize(db_file);
        if(pagesize<0) {
            printf("GG\n");
            exit(-1);
        }
        next_page_id_ = pagesize / PAGE_SIZE;
    };

    ~DiskManager() { db_io_.close(); }

    /* write system call */
    void WritePage(page_id_t page_id, const char *page_data){
        uint64_t offset = page_id * PAGE_SIZE;
        db_io_.seekp(offset);

        /* 每一次都是写一个page下去，IO层本来也是page，这里直接写的是二进制 */
        db_io_.write(page_data, PAGE_SIZE);

        if (db_io_.bad()) {
            std::cerr << "I/O error while writing" << std::endl;
            return;
        }

        db_io_.flush();  /* buffered write + fsync = direct IO */
    };

    void ReadPage(page_id_t page_id, char *page_data){
        uint64_t offset = page_id * PAGE_SIZE;
        // check if read beyond file length
        if (offset > GetFileSize(file_name_)) {
            std::cerr
                << "I/O error while reading offset: " << offset 
                << " over file size: " << GetFileSize(file_name_) << std::endl;
            exit(-1);
        } else {
            db_io_.seekp(offset);
            db_io_.read(page_data, PAGE_SIZE);
            int read_count = db_io_.gcount();  /* Get character count */
            if (read_count < PAGE_SIZE) {
                memset(page_data + read_count, 0, PAGE_SIZE - read_count);
            }
        }
    };

    page_id_t AllocatePage() { return next_page_id_++; }
    void DeallocateOnePage() {
        if(next_page_id_>0) { next_page_id_--; }
    }
    void DeallocatePage(__attribute__((unused)) page_id_t page_id) {return;}
    page_id_t GetPageId() const {return next_page_id_;}

private:
    uint64_t GetFileSize(const std::string &file_name) const {
        /* bytes */
        struct stat stat_buf;
        int rc = stat(file_name.c_str(), &stat_buf);
        return rc == 0 ? stat_buf.st_size : -1;
    }

    // stream to write db file
    std::fstream db_io_;  /* 表示输入文件流 */
    std::string file_name_;
    std::atomic<page_id_t> next_page_id_;  /* 代表文件偏移 */
};

/*
 * 手动管理 page cache in user
*/
class BufferPoolManager {
public:
	BufferPoolManager(size_t pool_size, DiskManager *disk_manager) : 
        pool_size_(pool_size), 
        disk_manager_(disk_manager) 
    {
        pages_ = new Page[pool_size_];
        free_list_ = new std::list<Page *>;
        
        replacer_ = new LRUReplacer<Page *>;
        // 可扩展的hash表, page id 与 page 的 kv
        page_table_ = new ExtendibleHash<page_id_t, Page *>(EXTRA_BUCKET_SIZE);  // EXTRA_BUCKET_SIZE is 50

        for (size_t i = 0; i < pool_size_; ++i) {
            free_list_->push_back(&pages_[i]);
        }
    }

	~BufferPoolManager(){
        delete[] pages_;
        delete page_table_;
        delete replacer_;
        delete free_list_;
    }

	// disable copy
	BufferPoolManager(BufferPoolManager const &) = delete;
	BufferPoolManager &operator=(BufferPoolManager const &) = delete;

    /* for read，offset一定在 file 范围内，本质是一个读操作 */
	Page *FetchPage(page_id_t page_id) {
        assert(page_id != INVALID_PAGE_ID);
        std::lock_guard<std::mutex> lock(mutex_);

        Page *res = nullptr;
        if (page_table_->Find(page_id, res)){
            return res;
        } else {
            /* id没有对应的page被使用 */
            if (!free_list_->empty()){
                /* list容器中有元素，说明还有空闲的page */
                res = free_list_->front();  /* 第一个元素的ref */
                free_list_->pop_front();  /* 删除容器头部的第一个元素 */
            } else {
                /* 没有空页了，需要执行页面替换算法，把一部分数据丢到disk */
                if (!replacer_->Victim(res)){
                    return nullptr;
                }
            }
        }

        if (res->is_dirty_) {
            /* 脏页写回 */
            disk_manager_->WritePage(res->page_id_, res->GetData());
        }
        // delete the entry for old page in hash table
	    page_table_->Remove(res->page_id_);

        // insert an entry for the new page in hash table
	    page_table_->Insert(page_id, res);  // 这里是可能导致rehash的

        // initial meta data
        res->page_id_ = page_id;
        res->is_dirty_ = false;
        res->pin_count_ = 1;
        disk_manager_->ReadPage(page_id, res->GetData());

        return res;
    }

    /* 用完了，要unpin一下 */
    bool UnpinPage(page_id_t page_id, bool is_dirty) {
        std::lock_guard<std::mutex> lock(mutex_);

        Page *res = nullptr;
        if (!page_table_->Find(page_id, res)){
            return false;
        }
        else {
            if (res->pin_count_ > 0){
                assert(1==res->pin_count_);
                if (--res->pin_count_ == 0){
                    /* page最近刚使用过，所以插入到LRU的表头中 */
                    replacer_->Insert(res);
                }
            }
            else{
                return false;
            }

            if (is_dirty){
                res->is_dirty_ = true;
            }
            return true;
        }
    }

    /* 刷所有的脏页，自己加的 */
    bool FlushAllDirtyPage() {
        /* fsync all db file */
        size_t i;
        Page *res = nullptr;

        for(i=0; i < pool_size_; ++i){
            res = pages_ + i;
            if(res->is_dirty_) {
                /* 如果这个page是被替换下来的，那么它一定是个脏的 */
                disk_manager_->WritePage(res->page_id_, res->GetData());
            }
        }
    }

    /*
    * Used to flush a particular page of the buffer pool to disk. Should call the
    * write_page method of the disk manager
    * if page is not found in page table, return false
    * NOTE: make sure page_id != INVALID_PAGE_ID
    */
    bool FlushPage(page_id_t page_id)
    {
        /* just like fsync */
        std::lock_guard<std::mutex> lock(mutex_);

        if (page_id == INVALID_PAGE_ID)
            return false;

        Page *res = nullptr;
        if (page_table_->Find(page_id, res)){
            disk_manager_->WritePage(page_id, res->GetData());
            return true;
        }
        return false;
    }

    /* 本质是写 */
    Page *NewPage(page_id_t &page_id) {
        std::lock_guard<std::mutex> lock(mutex_);

        Page *res = nullptr;
        if(!free_list_->empty()){
            res = free_list_->front();  /* 从空闲list中取一个page下来 */
            free_list_->pop_front();
        } else {
            if(!replacer_->Victim(res)){
                // 直接从LRU list中取下一个page来，
                return nullptr;
            }
        }

        /* 磁盘数据库文件的offset需增加一个page */
        page_id = disk_manager_->AllocatePage();  
        if(res->is_dirty_){
            /* 如果这个page是被替换下来的，那么它一定是个脏的 */
            disk_manager_->WritePage(res->page_id_, res->GetData());
        }

        page_table_->Remove(res->page_id_);
        page_table_->Insert(page_id, res);

        res->page_id_ = page_id;
        res->is_dirty_ = false;
        res->pin_count_ = 1;
        res->ResetMemory();

        return res;
    }

	// bool DeletePage(page_id_t page_id);
private:
	size_t pool_size_;
	Page *pages_;
	std::list<Page *> *free_list_;
	HashTable<page_id_t, Page *> *page_table_;
    Replacer<Page *> *replacer_;
	DiskManager *disk_manager_;
    std::mutex mutex_;
};

class StorageEngine {
public:
    StorageEngine(std::string db_file_name) {
        disk_manager_ = new DiskManager(db_file_name);
        buffer_pool_manager_ = new BufferPoolManager(BUFFER_POOL_SIZE, disk_manager_);
    }

    ~StorageEngine() {
        delete disk_manager_;
        delete buffer_pool_manager_;
    }

    DiskManager *disk_manager_;
    BufferPoolManager *buffer_pool_manager_;
};

/**
 * 采用最简单的文件组织方式，tuple head
 * 每一张表由一个 tuple head 表示
 */
class TableHeap {
public:
    TableHeap() = default;
    // create table heap
    TableHeap(
        BufferPoolManager *_buffer_pool_manager): buffer_pool_manager(_buffer_pool_manager)
    {
        /**
         * 构造函数，磁盘管理器会为table分配page，NewPage将以引用的形式接收 first_page_id
         * new page should be reset 
         */
        auto first_page =
            static_cast<TablePage *>(buffer_pool_manager->NewPage(first_page_id));
        assert(first_page != nullptr);
        first_page->WLatch();
        // init page layout
        first_page->Init(first_page_id, PAGE_SIZE, INVALID_PAGE_ID);
        /* debug 跑一个测试, 检查一下 init 之后的状态 */
        // CheckTablePage(first_page);
        first_page->WUnlatch();
        /* 2th para means if dirty */
        buffer_pool_manager->UnpinPage(first_page_id, true);
    }

    TableHeap(
        BufferPoolManager *_buffer_pool_manager, page_id_t _first_page_id): 
        buffer_pool_manager(_buffer_pool_manager), first_page_id(_first_page_id)
    {
        auto first_page =
            static_cast<TablePage *>(buffer_pool_manager->FetchPage(first_page_id));
        assert(first_page != nullptr);
    }

    ~TableHeap() {}

    bool InsertTuple(const Tuple &tuple, int index)
    {
        // for insert, if tuple is too large (>~page_size), return false
        // 队首的元数据占32字节
        if(tuple.GetSize() + 32 > PAGE_SIZE){
            printf("InsertTuple: one tuple is too large!\n", tuple.GetSize() + 32);
            return false;
        }

        /* 获取table对应的第一个page */
        auto cur_page = static_cast<TablePage *>(buffer_pool_manager->FetchPage(first_page_id));
        if (cur_page == nullptr) {
            printf("InsertTuple: no page to get!\n");
            return false;
        }

        cur_page->WLatch();
        while (!cur_page->InsertTuple(tuple, index)) {
            /**
             * fail to insert due to not enough space
             * 这个索引是线性扫过去的
             */
            page_id_t next_page_id = cur_page->GetNextPageId();
            if (INVALID_PAGE_ID == next_page_id) {
                // create new page
                auto new_page =
                    static_cast<TablePage *>(buffer_pool_manager->NewPage(next_page_id));
                if (new_page == nullptr) {
                    cur_page->WUnlatch();
                    buffer_pool_manager->UnpinPage(cur_page->GetPageId(), false);
                    return false;
                }
                new_page->WLatch();
                // std::cout << "new table page " << next_page_id << " created" << std::endl;
                /* 利用list将page都连接起来 */
                cur_page->SetNextPageId(next_page_id);
                new_page->Init(next_page_id, PAGE_SIZE, cur_page->GetPageId());
                cur_page->WUnlatch();
                buffer_pool_manager->UnpinPage(cur_page->GetPageId(), true);
                cur_page = new_page;
            } else { 
                // valid next page
                // 目前的实验环境下这里不会跑到
                cur_page->WUnlatch();
                buffer_pool_manager->UnpinPage(cur_page->GetPageId(), false);
                /* 换一个 page */
                cur_page = static_cast<TablePage *>(
                    buffer_pool_manager->FetchPage(next_page_id));
                cur_page->WLatch();
            }
        }

        cur_page->WUnlatch();
        buffer_pool_manager->UnpinPage(cur_page->GetPageId(), true);
        return true;
    }

    /**
     * table heap 代表一个 table, 这个对象负责整个表的组织方式
     */
    bool UpdateTuple(const Tuple &tuple, int index)
    {
        /* 遍历 table 的 page，找到对应的 page 先 */
        auto cur_page = static_cast<TablePage *>(buffer_pool_manager->FetchPage(first_page_id));

        cur_page->WLatch();
        while(!cur_page->UpdateTuple(tuple, index))
        {
            // get next page id
            page_id_t next_page_id = cur_page->GetNextPageId();
            if(next_page_id == INVALID_PAGE_ID){
                return false;
            } else {
                cur_page->WUnlatch();
                buffer_pool_manager->UnpinPage(cur_page->GetPageId(), false);
                cur_page = static_cast<TablePage *>(
                    buffer_pool_manager->FetchPage(next_page_id));
                cur_page->WLatch();  /* 继续执 while 循环 */
            }
        }

        buffer_pool_manager->UnpinPage(cur_page->GetPageId(), true);
        cur_page->WUnlatch();
        return true;
    }

    bool GetTuple(Tuple &tuple, int index)
    {
        auto cur_page = \
            static_cast<TablePage *>(buffer_pool_manager->FetchPage(first_page_id));

        cur_page->WLatch();
        while(!cur_page->GetTuple(tuple, index))
        {
            page_id_t next_page_id = cur_page->GetNextPageId();
            if(next_page_id == INVALID_PAGE_ID){
                return false;
            } else {
                cur_page->WUnlatch();
                buffer_pool_manager->UnpinPage(cur_page->GetPageId(), false);
                cur_page = static_cast<TablePage *>(
                    buffer_pool_manager->FetchPage(next_page_id));
                cur_page->WLatch();
            }
        }

        buffer_pool_manager->UnpinPage(cur_page->GetPageId(), true);
        cur_page->WUnlatch();
        return true;
    }

    inline page_id_t GetFirstPageId() const { return first_page_id; }

private:
    BufferPoolManager *buffer_pool_manager;
    page_id_t first_page_id;
    friend void CheckTablePage(TablePage *);
};


/**
 * 正好整合一下那几个属性
 * 操作基本上都全部整合到了 table_heap 上
 */
class DBTable
{
public:
    DBTable()=default;

    // create
    DBTable(
        BufferPoolManager* _buffer_pool_manager, 
        DiskManager* _disk_manager, 
        std::string& _tbname,
        int _encBlockSize, int _rownum, int _type, int _cursor, Schema* _schema):
        buffer_pool_manager(_buffer_pool_manager), disk_manager(_disk_manager), tablename(_tbname),
        encBlockSize(_encBlockSize), rownum(_rownum), type(_type), cursor(_cursor)
    {
        memcpy(&schema, _schema, sizeof(Schema));
        table_heap = new TableHeap(buffer_pool_manager);
    }

    // reopen
    DBTable(
        BufferPoolManager* _buffer_pool_manager, 
        DiskManager* _disk_manager, 
        std::string& _tbname,
        int _encBlockSize, int _rownum, int _type, int _cursor, page_id_t first_page_id, Schema* _schema):
        buffer_pool_manager(_buffer_pool_manager), disk_manager(_disk_manager), tablename(_tbname),
        encBlockSize(_encBlockSize), rownum(_rownum), type(_type), cursor(_cursor)
    {
        assert(cursor==rownum);
        memcpy(&schema, _schema, sizeof(Schema));
        table_heap = new TableHeap(buffer_pool_manager, first_page_id);
    }

    ~DBTable() { delete table_heap; }

    bool InsertTuple(const Tuple &tuple, int index) { 
        return table_heap->InsertTuple(tuple, index); 
    }

    bool UpdateTuple(const Tuple &tuple, int index) { 
        return table_heap->UpdateTuple(tuple, index); 
    }

    bool GetTuple(Tuple& tuple, int index){
        return table_heap->GetTuple(tuple, index);
    }

    int TableSize() const { return rownum; }
    int Cursor() const { return cursor; }
    void IncrementCursor() { cursor++; }
    TableHeap* GetTableHeap() const { return table_heap; }
    void DeallocateOnePage() { disk_manager->DeallocateOnePage(); }
    std::string& TableName() { return tablename; }
    int Type() const { return type; }

    Schema* GetSchema() { return &schema; } 
private:
    std::string tablename;
    BufferPoolManager* buffer_pool_manager;
    DiskManager* disk_manager;
    int encBlockSize;
    int rownum;
    int type;
    TableHeap* table_heap;  /* table head 几乎是最简单的数据库文件组织方式 */
    Schema schema;

    /* 代表目前准备写位置的下标，每张表只写一次，游标就用一次，init一次，为 real write 准备 */
    int cursor;  
};
/***********************/
} // namespace oblidbextraio


namespace utility{
void split(const std::string& str, 
           std::vector<std::string>& tokens, 
           const char delim=' ') 
{
    tokens.clear();
    
    std::istringstream iss(str);
    std::string tmp;
    while (std::getline(iss, tmp, delim)) {
        if (tmp != "") {
            // 如果两个分隔符相邻，则 tmp == ""，忽略。
            tokens.emplace_back(std::move(tmp));
        }
    }
}
}  // namespace utility


namespace attacker {

typedef ssize_t Tsize;  /* size of 输入表 */
typedef ssize_t Rsize;  /* size of 结果表 */

typedef struct CURSOR{
    int whichloop;
    int begin;
} cursor;

/**
 * 还没有太想好基类中放什么内容
 */
// template <class T>
class Attacker
{
public:
    Attacker(){};
    virtual ~Attacker(){};
};

/**
 * select * from orderd where seq between 20 and 45
 * low value: 20
 * high value: 45
 */
// template <class T>

class OblidbContinueAttack : public Attacker
{
public:
    OblidbContinueAttack(OblidbContinueAttack const &)=delete;
    OblidbContinueAttack& operator=(OblidbContinueAttack const &)=delete;

    explicit OblidbContinueAttack(
        ssize_t _blocksize, Tsize _insize, 
        Rsize _outsize, uint8_t* _ttable, 
        uint8_t* _rtable, uint64_t _range_low, uint64_t _range_high):
        blocksize(_blocksize), insize(_insize), outsize(_outsize), 
        ttable(_ttable), rtable(_rtable), range_low(_range_low), range_high(_range_high)
    {
        // 暂存调序后的输入表
        tmpttable = (uint8_t*)malloc(blocksize * insize);
        // 暂存调序后的结果表
        tmprtable = (uint8_t*)malloc(blocksize * outsize);

        // 步长的初始值与结果表大小一致
        step = outsize;
    }

    explicit OblidbContinueAttack(
        uint8_t* _reordertable) : reordertable(_reordertable)
    {
        step = outsize;
    }

    virtual ~OblidbContinueAttack()
    {
        // 有机会再换智能指针的写法
        if(tmpttable){
            free(tmpttable);
        }
        if(tmprtable){
            free(tmprtable);
        }
    }

    void ReorderTable(int begin){
        void* src;
        void* dst;
        int end = (begin + step) % insize;  // 被选出来的下标，end不是采样下标

        if(begin > end){ // 闭环了
            for(int index=0;index<insize;++index){
                src = reinterpret_cast<void *>((ttable + index*blocksize));

                if(index < end){ // 采样数据, 在table的最末端
                    dst = reinterpret_cast<void *>((tmpttable + (insize-end+index)*blocksize));
                } else if (index>=end && index<begin){ // 整体前移的数据
                    dst = reinterpret_cast<void *>((tmpttable + (index-end)*blocksize));
                } else { // 采样数据
                    dst = reinterpret_cast<void *>((tmpttable + (index-end)*blocksize));
                }

                memcpy(dst, src, blocksize);
            }
        } else { // normal
            for(int index=0;index<insize;++index){
                src = reinterpret_cast<void *>((ttable + index*blocksize));

                if(index < begin){
                    dst = reinterpret_cast<void *>((tmpttable + index*blocksize));
                } else if (index >= begin && index < end){
                    dst = reinterpret_cast<void *>((tmpttable + (insize-step+index-begin)*blocksize));
                } else {
                    dst = reinterpret_cast<void *>((tmpttable + (index-step)*blocksize));
                }

                memcpy(dst, src, blocksize);
            }
        }
    }

    int SelectRows(){
        char line[blocksize];
        int begin;
        const char delim = ',';
        std::vector<std::string> tokens;
        uint64_t num;

        for(int i=0;i<insize;++i){
            memcpy((void *)line, (void *)(tmpttable + i*blocksize), blocksize);
            // std::cout << i << ":" << line << std::endl;
            // 判断目标的value是否是范围查询的起始位置
            std::string str(line);
            utility::split(str, tokens, delim);
            // printf("after split\n");
            // for(auto i=tokens.begin(); i!=tokens.end();++i){
            //     std::cout << *i << std::endl;
            // }
            // printf("after print tokens\n");
            num = atoi(tokens[2].c_str());
            if(num == range_low){
                begin = i;
                break;
            }
        }

        void *dst;
        void *src;

        for(int j=begin;j<begin+outsize;++j){
            // printf("j-begin is: %d  j%T is %d\n", j-begin, j%T);
            dst = reinterpret_cast<void *>((tmprtable + (j-begin)*blocksize));
            src = reinterpret_cast<void *>((tmpttable + (j%insize)*blocksize));
            // std::cout << "  dst: " << (char*)dst << " " << "src: " << (char*)src << std::endl;
            memcpy(dst, src, blocksize);
        }
        return begin;
    }

    bool SameRet() const {
        bool ret = true;
        for(int i=0;i<outsize; ++i){
            char* dstv = reinterpret_cast<char *>(rtable + i*blocksize);
            char* srcv = reinterpret_cast<char *>(tmprtable + i*blocksize);
            std::string _dstv(dstv);
            std::string _srcv(srcv);

            // std::cout << "dst: " << _dstv << " " << "src: " << _srcv << std::endl;
            if(_dstv.compare(_srcv) != 0){
                ret = false;
                break;
            }
        }
        return ret;
    }

    void RollCheck(){
        cursor _cursor;
        _cursor.begin = 0;
        _cursor.whichloop = 0;

        while(step){
            _Rollback(this, _cursor, _cursor.whichloop);
            printf("Step:%d, Begin:%d, Loop index:%d\n", step, _cursor.begin, _cursor.whichloop);
            step /= 2;
        }
    }

private:
    ssize_t blocksize;
    Tsize insize;
    Rsize outsize;

    /* 外部管理内存 */
    uint8_t* ttable;
    uint8_t* rtable;

    /* 类内管理内存 */
    uint8_t* tmpttable;
    uint8_t* tmprtable;

    uint64_t range_low;
    uint64_t range_high;

    int step;  /* 每次检查的步长 */

    // 临时表的内存空间由 app 自己 联合 sgx 共同管理，尽量减少攻击外要素的影响
    uint8_t* reordertable;

    friend void _Rollback(OblidbContinueAttack*, cursor&, int);
};

class OblidbContinueAttackTest
{
public:
    OblidbContinueAttackTest(
        uint64_t _begin, uint64_t _end) : begin(_begin), end(_end)
    {
        // TODO 边界条件的检测
        size = end-begin+1;
    }
    ~OblidbContinueAttackTest(){};

    size_t Begin() const {return begin;}
    size_t End() const {return end;}
    size_t Size() const {return size;}
private:
    uint64_t begin;
    uint64_t end;
    uint64_t size;
};

void
_Rollback(OblidbContinueAttack* ths, cursor& _cursor, int loopindex)
{
    uint64_t begin;
    // 这里的j不一定要由0开始，可以利用之前得到的结果优化，少一些循环
    for(int j=loopindex;j<ths->insize;++j){
        ths->ReorderTable(j);
        begin=ths->SelectRows();

        if(!ths->SameRet()){
            _cursor.begin = begin;
            _cursor.whichloop = j;
            break;
        }
    }
}

class AttackWindow
{
public:
    explicit AttackWindow(bool _attackflag): attackflag(_attackflag) 
    {
        hitflag = false;
    }
    virtual ~AttackWindow(){}

    AttackWindow(AttackWindow const&)=delete;
    AttackWindow& operator=(AttackWindow const&)=delete;

    bool GetFlag() const { return attackflag; }
    void SetFlag(bool _flag) { attackflag=_flag; }

    bool GetHitFlag() const { return hitflag; }
    void SetHitFlag(bool _hitflag) { hitflag = _hitflag; }
private:
    bool attackflag;
    bool hitflag;
};
} // namespace attacker