
#include "config_pc.hpp"
#include "merkle_tree.h"
#include <vector>
#include <math.h>
#include <omp.h>
#include "virgo_prime_field.h"
#include "fieldElement.hpp"
#include <unistd.h>

using namespace std;

int merkle_tree::size_after_padding;


void merkle_tree::get_int32(vector<unsigned int> &arr, __hhash_digest hash){
    unsigned int* res_array = reinterpret_cast<unsigned int*>(&hash.h0);
    for (int i = 0; i < 4; ++i) {
        arr[i] = res_array[i];
    }
    res_array = reinterpret_cast<unsigned int*>(&hash.h1);
    for(int i = 4; i < 8; i++){
        arr[i] = res_array[i-4];        
    }
}


__hhash_digest merkle_tree::_hash_double_field_element_merkle_damgard(prime_field::field_element x, prime_field::field_element y, __hhash_digest prev_hash)
{
   __hhash_digest data[2], ret;
    data[0] = prev_hash;
    prime_field::field_element element[2];
    element[0] = x;
    element[1] = y;
    memcpy(&data[1], element, 2 * sizeof(prime_field::field_element));
    assert(2 * sizeof(prime_field::field_element) == sizeof(__hhash_digest));
    my_hhash(data, &ret);
    return ret;
}


__hhash_digest merkle_tree::hash_double_field_element_merkle_damgard(virgo::fieldElement x, virgo::fieldElement y, virgo::fieldElement z, virgo::fieldElement w, __hhash_digest prev_hash)
{
   __hhash_digest data[2], ret;
    //data[0] = prev_hash;
    virgo::fieldElement element[2];
    element[0] = x;
    element[1] = y;
    memcpy(&data[0], element, 2 * sizeof(virgo::fieldElement));
    element[0] = z;
    element[1] = w;
    memcpy(&data[1], element, 2 * sizeof(virgo::fieldElement));
    //printf("%d %d\n",4 * sizeof(virgo::fieldElement),sizeof(__hhash_digest));
    //assert(2 * sizeof(virgo::field_element) == sizeof(__hhash_digest));
    my_hhash(data, &ret);
    data[0] = ret;
    data[1] = prev_hash;
    my_hhash(data, &ret);
    return ret;
}

_hash merkle_tree::hash_double_field_element_merkle_damgard_blake(virgo::fieldElement x, virgo::fieldElement y, virgo::fieldElement z, virgo::fieldElement w, _hash &prev_hash)
{
    uint8_t data[64];
    _hash ret;
    //data[0] = prev_hash;
    virgo::fieldElement element[2];
    element[0] = x;
    element[1] = y;
    memcpy(data, element, 2 * sizeof(virgo::fieldElement));
    element[0] = z;
    element[1] = w;
    memcpy(data + 32, element, 2 * sizeof(virgo::fieldElement));
    //printf("%d %d\n",4 * sizeof(virgo::fieldElement),sizeof(__hhash_digest));
    //assert(2 * sizeof(virgo::field_element) == sizeof(__hhash_digest));
    blake3_hash(data, ret.arr);
    for(int i = 0; i < 32; i++){
        data[i] = ret.arr[i];
    }
    for(int i = 0; i < 32; i++){
        data[32+i] = prev_hash.arr[i];
    }
    //data[0] = ret;
    //data[1] = prev_hash;
    blake3_hash(data, ret.arr);
    return ret;
}
    
void merkle_tree::merkle_tree_prover::_create_tree(void* src_data, int ele_num, __hhash_digest* &dst, const int element_size = 256 / 8, bool alloc_required = false)
{
    //assert(element_size == sizeof(prime_field::field_element) * 2);
    size_after_padding = 1;
    while(size_after_padding < ele_num)
        size_after_padding *= 2;

    __hhash_digest *dst_ptr;
    if(alloc_required)
    {
        dst_ptr = (__hhash_digest*)malloc(size_after_padding * 2 * element_size);
        if(dst_ptr == NULL)
        {
            printf("Merkle Tree Bad Alloc\n");
            abort();
        }
    }
    else
        dst_ptr = dst;
    //线段树要两倍大小
    dst = dst_ptr;
    memset(dst_ptr, 0, size_after_padding * 2 * element_size);

    int start_ptr = size_after_padding;
    int current_lvl_size = size_after_padding;
    #pragma omp parallel for
    for(int i = current_lvl_size - 1; i >= 0; --i)
    {
        __hhash_digest data[2];
        memset(data, 0, sizeof data);
        if(i < ele_num)
        {
            dst_ptr[i + start_ptr] = ((__hhash_digest*)src_data)[i];
        }
        else
        {
            memset(data, 0, sizeof data);
            my_hhash(data, &dst_ptr[i + start_ptr]);
        }
    }
    current_lvl_size /= 2;
    start_ptr -= current_lvl_size;
    while(current_lvl_size >= 1)
    {
        #pragma omp parallel for
        for(int i = 0; i < current_lvl_size; ++i)
        {
            __hhash_digest data[2];
            data[0] = dst_ptr[start_ptr + current_lvl_size + i * 2];
            data[1] = dst_ptr[start_ptr + current_lvl_size + i * 2 + 1];
            my_hhash(data, &dst_ptr[start_ptr + i]);
        }
        current_lvl_size /= 2;
        start_ptr -= current_lvl_size;
    }
    delete[] dst_ptr;
}

void merkle_tree::merkle_tree_prover::create_tree_sha(int ele_num, vector<vector<__hhash_digest>> &dst_ptr, int level, const int element_size = 256 / 8, bool alloc_required = false){
    int current_lvl_size = ele_num;
    //#pragma omp parallel for
   
    int curr_level = 1;
    current_lvl_size /= 2;
    while(curr_level != level)
    {
        //printf("%d,%d,%d\n",current_lvl_size,dst_ptr[curr_level].size(),curr_level);
        #pragma omp parallel for
        for(int i = 0; i < current_lvl_size; ++i)
        {
            //printf("%d,%d\n",start_ptr + current_lvl_size + i * 2,start_ptr + current_lvl_size + i * 2+1);
            __hhash_digest data[2];
            data[0] = dst_ptr[curr_level-1][i * 2];
            data[1] = dst_ptr[curr_level-1][i * 2 + 1];
            my_hhash(data, &dst_ptr[curr_level][i]);
        }
        curr_level++;
        current_lvl_size /= 2;
    }
}

void merkle_tree::merkle_tree_prover::MT_commit(F *leafs,vector<vector<__hhash_digest>> &hashes, int N){
    vector<__hhash_digest> leaf_hashes(N/4);
    __hhash_digest data[2], ret;
    //data[0] = prev_hash;
    virgo::fieldElement element[2];
   #pragma omp parallel for
   for(int i = 0; i < N/4; i++){
        element[0] = leafs[4*i];
        element[1] = leafs[4*i+1];
        memcpy(&data[0], element, 2 * sizeof(virgo::fieldElement));
        element[0] = leafs[4*i+2];
        element[1] = leafs[4*i]+3;
        memcpy(&data[1], element, 2 * sizeof(virgo::fieldElement));
        my_hhash(data, &leaf_hashes[i]);
    }
    
    if(hashes.size() == 0){
        hashes.resize((int)log2(leaf_hashes.size())+1);
    }
    hashes[0] = leaf_hashes;
    merkle_tree::merkle_tree_prover::create_tree( leaf_hashes.size(), hashes, sizeof(__hhash_digest), true);
}

void merkle_tree::merkle_tree_prover::MT_commit_Blake(F *leafs,vector<vector<_hash>> &hashes, int N){
    //vector<vector<uint8_t>> leaf_hashes(N/4);
    
    //for(int  i= 0; i < leaf_hashes.size(); i++){
    //    leaf_hashes[i].resize(32);
    //}
    uint8_t data[2*32], ret;
    //data[0] = prev_hash;
    virgo::fieldElement element[2];
    if(hashes.size() == 0){
        hashes.resize((int)log2(N/4)+1);
    }
    hashes[0].resize(N/4);
   #pragma omp parallel for
   for(int i = 0; i < N/4; i++){
        element[0] = leafs[4*i];
        element[1] = leafs[4*i+1];
        memcpy(data, element, 2 * sizeof(virgo::fieldElement));
        element[0] = leafs[4*i+2];
        element[1] = leafs[4*i+3];
        //hashes[0][i].resize(32);
        memcpy(data + 32, element, 2 * sizeof(virgo::fieldElement));
        blake3_hash(data, hashes[0][i].arr);
    }
    
    merkle_tree::merkle_tree_prover::create_tree_blake( hashes[0].size(), hashes, sizeof(__hhash_digest), true);
    
    
}


__hhash_digest merkle_tree::merkle_tree_prover::create_tree(int ele_num, vector<vector<__hhash_digest>> &hashes, const int element_size = 256 / 8, bool alloc_required = false)
{
    //assert(element_size == sizeof(prime_field::field_element) * 2);
    
    int current_lvl_size = ele_num;
    
    int level = 1;
    current_lvl_size /= 2;
    __hhash_digest data[2];
    int lvl = 1;
    
    while(current_lvl_size >= 1)
    {
        if(lvl >= 0){
            hashes[lvl].resize(current_lvl_size);
        }
        #pragma omp parallel for
        for(int i = 0; i < current_lvl_size; ++i)
        {
            //printf("%d,%d\n",start_ptr + current_lvl_size + i * 2,start_ptr + current_lvl_size + i * 2+1);
            data[0] = hashes[lvl-1][ i * 2];
            data[1] = hashes[lvl-1][ i * 2 + 1];
            my_hhash(data, &hashes[lvl][i]);
        }
        lvl++;
        current_lvl_size /= 2;
    }
    //dst = dst_ptr.data();
    return hashes[hashes.size()-1][0];
}

void merkle_tree::merkle_tree_prover::create_tree_blake(int ele_num, vector<vector<_hash>> &hashes, const int element_size = 256 / 8, bool alloc_required = false)
{
    //assert(element_size == sizeof(prime_field::field_element) * 2);
    
    int current_lvl_size = ele_num;
    
    int level = 1;
    current_lvl_size /= 2;
    uint8_t data[64];
    int lvl = 1;
    
    while(current_lvl_size >= 1)
    {
        if(lvl >= 0){
            hashes[lvl].resize(current_lvl_size);
        }
        #pragma omp parallel for
        for(int i = 0; i < current_lvl_size; ++i)
        {
            //printf("%d,%d\n",start_ptr + current_lvl_size + i * 2,start_ptr + current_lvl_size + i * 2+1);
            for(int j = 0; j  < 32; j++){
                data[j] = hashes[lvl-1][ i * 2].arr[j];
            }
            for(int j = 0; j < 32; j++){
                data[j+32] = hashes[lvl-1][ i * 2].arr[j];
            }
            //hashes[lvl][i].resize(32);
            blake3_hash(data, hashes[lvl][i].arr);
        }
        lvl++;
        current_lvl_size /= 2;
    }
}


vector<__hhash_digest> merkle_tree::merkle_tree_prover::open_tree(vector<vector<__hhash_digest>> &MT_hashes, vector<size_t> c,  int collumns){
    int pos = (c[1]/4)*collumns + c[0];
    if(pos >= MT_hashes[0].size()){
        printf("Error %d,%d\n",pos,MT_hashes[0].size());
        exit(-1);
    }
    vector<__hhash_digest> path;
    for(int i = 0; i < MT_hashes.size()-1; i++){
        if((2*(pos/2) + (1-(pos%2))) >= MT_hashes[i].size()){
            printf("Error in open %d %d,%d\n",pos^1,i,MT_hashes[i].size());
            exit(-1);
        }
        path.push_back(MT_hashes[i][2*(pos/2) + (1-(pos%2))]);
        pos = pos/2;
    }
    return path;
}

vector<_hash> merkle_tree::merkle_tree_prover::open_tree_blake(vector<vector<_hash>> &MT_hashes, vector<size_t> c,  int collumns){
    int pos = (c[1]/4)*collumns + c[0];
    if(pos >= MT_hashes[0].size()){
        printf("Error %d,%d\n",pos,MT_hashes[0].size());
        exit(-1);
    }
    vector<_hash> path;
    for(int i = 0; i < MT_hashes.size()-1; i++){
        if((2*(pos/2) + (1-(pos%2))) >= MT_hashes[i].size()){
            printf("Error in open %d %d,%d\n",pos^1,i,MT_hashes[i].size());
            exit(-1);
        }
        path.push_back(MT_hashes[i][2*(pos/2) + (1-(pos%2))]);
        pos = pos/2;
    }
    return path;
}

bool merkle_tree::merkle_tree_verifier::verify_claim_opt_blake(vector<vector<_hash>> &MT, const _hash* path, int pos_element_arr, int N,  bool *visited, double &ps)
{
   //check N is power of 2
    assert((N & (-N)) == N);
    
    int pos = pos_element_arr;
    
    if(pos >= MT[0].size()){
        printf("Error %d,%d\n",pos,MT[0].size());
        exit(-1);
    }
    int pos_element = N+pos_element_arr;
    _hash leaf_hash = path[0];
    _hash data[2];
    for(int i = 0; i < MT.size()-1; i++){
        
        
        if(!visited[pos_element ^ 1]){
            data[pos & 1] = leaf_hash;
            data[(pos & 1) ^ 1] = MT[i][pos ^ 1];
            //printf("%d,%d\n",pos_element,pos_element ^ 1 );
            //exit(-1);
            my_hhash(data, &leaf_hash);
            visited[pos_element ^ 1] = true;
            pos_element /= 2;
            pos /= 2;
            visited[pos_element] = true;
            ps += 32.0/1024.0;
        }else{
            return true;
        }
    }

    return true;
}



bool merkle_tree::merkle_tree_verifier::verify_claim_opt(vector<vector<__hhash_digest>> &MT, const __hhash_digest* path, int pos_element_arr, int N,  bool *visited, double &ps)
{
   //check N is power of 2
    assert((N & (-N)) == N);
    
    int pos = pos_element_arr;
    
    if(pos >= MT[0].size()){
        printf("Error %d,%d\n",pos,MT[0].size());
        exit(-1);
    }
    int pos_element = N+pos_element_arr;
    __hhash_digest leaf_hash = path[0];
    __hhash_digest data[2];
    for(int i = 0; i < MT.size()-1; i++){
        
        
        if(!visited[pos_element ^ 1]){
            data[pos & 1] = leaf_hash;
            data[(pos & 1) ^ 1] = MT[i][pos ^ 1];
            //printf("%d,%d\n",pos_element,pos_element ^ 1 );
            //exit(-1);
            my_hhash(data, &leaf_hash);
            visited[pos_element ^ 1] = true;
            pos_element /= 2;
            pos /= 2;
            visited[pos_element] = true;
            ps += (double)sizeof(__hhash_digest)/1024.0;
        }else{
            return true;
        }
    }

    return true;
}


bool merkle_tree::merkle_tree_verifier::verify_claim(__hhash_digest root_hhash, const __hhash_digest* tree, __hhash_digest leaf_hash, int pos_element_arr, int N)
{
    //check N is power of 2
    assert((N & (-N)) == N);

    int pos_element = pos_element_arr + N;
    __hhash_digest data[2];
    while(pos_element != 1)
    {
            data[pos_element & 1] = leaf_hash;
            data[(pos_element & 1) ^ 1] = tree[pos_element ^ 1];
            my_hhash(data, &leaf_hash);
            pos_element /= 2;
        
        
    }
    return equals(root_hhash, leaf_hash);
}