#pragma once
#ifndef __merkle_tree
#define __merkle_tree
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <immintrin.h>
#include <wmmintrin.h>
#include "my_hhash.h"
#include "Blake3_hash.h"
#include "virgo_prime_field.h"


namespace merkle_tree
{
extern int size_after_padding;

void get_int32(vector<unsigned int> &arr, __hhash_digest hash);

__hhash_digest hash_single_field_element(F x);

__hhash_digest hash_double_field_element_merkle_damgard(virgo::fieldElement x, virgo::fieldElement y, virgo::fieldElement z, virgo::fieldElement w, __hhash_digest prev_hash);
__hhash_digest _hash_double_field_element_merkle_damgard(prime_field::field_element x, prime_field::field_element y, __hhash_digest prev_hash);
//void hash_double_field_element_merkle_damgard_blake(virgo::fieldElement x, virgo::fieldElement y, virgo::fieldElement z, virgo::fieldElement w, uint8_t *prev_hash, uint8_t *ret);
_hash hash_double_field_element_merkle_damgard_blake(virgo::fieldElement x, virgo::fieldElement y, virgo::fieldElement z, virgo::fieldElement w, _hash &prev_hash);
namespace merkle_tree_prover
{
    //Merkle tree functions used by the prover
    //void create_tree(void* data_source_array, int lengh, void* &target_tree_array, const int single_element_size = 256/8)
    __hhash_digest create_tree(int ele_num, vector<vector<__hhash_digest>> &hashes, const int element_size, bool alloc_required);
    void _create_tree(void* src_data, int ele_num,__hhash_digest* &dst, const int element_size, bool alloc_required);
    void MT_commit(F *leafs,vector<vector<__hhash_digest>> &hashes, int N);
    void MT_commit_Blake(F *leafs,vector<vector<_hash>> &hashes, int N);
    void create_tree_mimc( int ele_num, vector<vector<F>> &dst_ptr, int level, const int element_size, bool alloc_required );
    void create_tree_sha( int ele_num, vector<vector<__hhash_digest>> &dst_ptr, int level, const int element_size, bool alloc_required);
    void create_tree_blake(int ele_num, vector<vector<_hash>> &hashes, const int element_size, bool alloc_required);
    vector<__hhash_digest> open_tree(vector<vector<__hhash_digest>> &MT_hashes, vector<size_t> c,  int collumns);
    vector<_hash> open_tree_blake(vector<vector<_hash>> &MT_hashes, vector<size_t> c,  int collumns);

}

namespace merkle_tree_verifier
{
    //Merkle tree functions used by the verifier
    bool verify_claim(__hhash_digest root_hhash, const __hhash_digest* tree, __hhash_digest hhash_element, int pos_element, int N);
    bool verify_claim_opt(vector<vector<__hhash_digest>> &MT, const __hhash_digest* path, int pos_element_arr, int N,  bool *visited, double &ps);
    bool verify_claim_opt_blake(vector<vector<_hash>> &MT, const _hash* path, int pos_element_arr, int N,  bool *visited, double &ps);

}
}

#endif