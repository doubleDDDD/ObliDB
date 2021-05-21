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
#include <mutex>  // 线程互斥体
#include <climits>

namespace oblidbextraio {
/***********************/

#define PAGE_SIZE 4096  // 与filesystem IO 一致
#define BUFFER_POOL_SIZE 32  // 很小，为了保证能够看到效果 16M
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
 *  -----------------------------------------------------------------
 * | RecordCount (4) | Entry_1 name (32) | Entry_1 root_id (4) | ... |
 *  -----------------------------------------------------------------
 */
class HeaderPage : public Page {
public:
    void Init() { SetRecordCount(0); }

    /* Record related */
    bool InsertRecord(const std::string &name, const page_id_t root_id){
        assert(name.length() < 32);
        assert(root_id > INVALID_PAGE_ID);

        int rnum = GetRecordCount();
        int offset = 4 + rnum * 36;

        /* check if offset is too large */
        if (PAGE_SIZE - offset < 36) { return false; }

        /* 检查重名 */
        if (FindRecord(name) != -1)
            return false;

        // copy record content
        memcpy(GetData() + offset, name.c_str(), (name.length() + 1));
        memcpy((GetData() + offset + 32), &root_id, 4);

        SetRecordCount(rnum + 1);
        return true;
    }

    bool DeleteRecord(const std::string &name){
        int rnum = GetRecordCount();
        assert(rnum > 0);

        int index = FindRecord(name);
        if(index == -1) {return false;}

        int offset = 4 + index * 36;
        /* 整体前移 */
        memmove(GetData() + offset, GetData() + offset + 36, (rnum - index - 1) * 36);
        SetRecordCount(rnum - 1);
        return true;
    };

    bool UpdateRecord(const std::string &name, const page_id_t root_id){
        assert(name.length() < 32);

        int index = FindRecord(name);
        if(index == -1) {return false;}

        int offset = 4 + index * 36;
        memcpy((GetData() + offset + 32), &root_id, 4);

        return true;
    }

    // return root_id if success
    bool GetRootId(const std::string &name, page_id_t &root_id) {
        assert(name.length() < 32);

        int index = FindRecord(name);
        if(index == -1) {return false;}

        /**
         * 0: 4 + 32:           36
         * 1: 4 + 36 + 32:      36*2
         * 2: 4 + 36 + 36 + 32  36*3
         */
        int offset = (index + 1) * 36;
        root_id = *reinterpret_cast<page_id_t *>(GetData() + offset);
    }

private:
    /* helper functions */
    int GetRecordCount(){
        /* GetData的前4个字节，直接 char* 转 int，int 4字节 */
        return *reinterpret_cast<int *>(GetData());
    }

    int FindRecord(const std::string &name){
        int i;
        size_t rnum = GetRecordCount();

        for(i=0; i<rnum; ++i){
            char *raw_name = reinterpret_cast<char *>(GetData() + (4 + i*36));
            if(strcmp(raw_name, name.c_str())==0) {return i;}
        }

        return -1;
    }

    void SetRecordCount(int record_count){
        memcpy(GetData(), &record_count, 4);
    }
};

/**
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
 * | PageId (4)| LSN (4, 保留)| PrevPageId (4)| NextPageId (4)| FreeSpacePointer(4) |
 *  --------------------------------------------------------------------------
 *  --------------------------------------------------------------
 * | TupleCount (4) | Tuple_1 offset (4) | Tuple_1 size (4) | ... |
 *  --------------------------------------------------------------
 * 在一个page中，tuple slot 从前向后增长，空闲空间从后先前增长。FreeSpacePointer 在初始化的时候是指向 page 的尾端的
 * 一个 tuple 的 slot 占 8 个字节
 * size=0 意味着是一个 empty slot
 * 如果是线性扫描的 page 的话，没有必要这样复杂
 * 因为一个 table 的里表都是等长的，page header 记录一下它有多长，起始index是多少，有几个就足够了
 */
class TuplePage : public Page {
public:
    /**
    * Header related
    */
    void Init(page_id_t page_id, size_t page_size, page_id_t prev_page_id){
        /* 按照上面的结构从前向后set */
        memcpy(GetData(), &page_id, 4);  /* set page id */
        SetPrevPageId(prev_page_id);
        SetNextPageId(INVALID_PAGE_ID);
        SetFreeSpacePointer(page_size);
        SetTupleCount(0);
    }

    page_id_t GetPageId(){
        return *reinterpret_cast<page_id_t *>(GetData());
    }

    page_id_t GetPrevPageId(){
        return *reinterpret_cast<page_id_t *>(GetData() + 8);
    }

    page_id_t GetNextPageId(){
        return *reinterpret_cast<page_id_t *>(GetData() + 12);
    }

    void SetPrevPageId(page_id_t prev_page_id){
        memcpy(GetData() + 8, &prev_page_id, 4);
    }

    void SetNextPageId(page_id_t next_page_id){
        memcpy(GetData() + 12, &next_page_id, 4);
    }

    /**
    * Tuple related
    */
    bool InsertTuple(int index, int blockSize, void *buffer){
        // check if free space is enough
        if(blockSize > GetFreeSpaceSize()){
            return false
        }
    }

private:
    /**
    * helper functions
    */
    int32_t GetTupleOffset(int slot_num){
        return *reinterpret_cast<int32_t *>(GetData()  + 24 + slot_num * 8);
    }

    int32_t GetTupleSize(int slot_num){
        return *reinterpret_cast<int32_t *>(GetData()  + 24 + slot_num * 8 + 4);
    }

    void SetTupleOffset(int slot_num, int32_t offset){
        char *begin = GetData()  + 24 + slot_num * 8;
        memcpy(begin, &offset, 4);
    }

    void SetTupleSize(int slot_num, int32_t offset){
        char *begin = GetData()  + 24 + slot_num * 8 + 4;
        memcpy(begin, &offset, 4);
    }

    int32_t GetFreeSpacePointer(){
        // offset of the beginning of free space
        return *reinterpret_cast<int32_t *>(GetData()  + 16);
    }

    void SetFreeSpacePointer(int32_t free_space_pointer){
        memcpy((GetData() + 16), &free_space_pointer, 4);
    }

    int32_t GetTupleCount(){
        // Note that this tuple count may be larger than # of
        return *reinterpret_cast<int32_t *>(GetData()  + 20);
    };

    // actual tuples because some slots may be empty
    void SetTupleCount(int32_t tuple_count){
        memcpy((GetData() + 20), &tuple_count, 4);
    }

    int32_t GetFreeSpaceSize(){
        return GetFreeSpacePointer() - (24 + 8 * GetTupleCount());
    }
}

/* 磁盘管理 */
class DiskManager {
public:
    DiskManager(const std::string &db_file) : file_name_(db_file), next_page_id_(0)
    {
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

/***********************/
} // namespace oblidbextraio