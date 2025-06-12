#pragma once
#include "expanders.h"
#include "linear_code_encode.h"
#include <math.h>
#include "utils.hpp"
#include "merkle_tree.h"

struct MT_proof{
    F sibling;
    size_t idx;
    vector<__hhash_digest> path;
    vector<bool> direction;
};

struct FRI_proof{
    F sibling;
    vector<vector<F>> query_points;
    vector<MT_proof> Proofs;
};

struct Virgo_proof{
    FRI_proof Fri;
    vector<MT_proof> query_paths;
    vector<vector<F>> query_points;
};

struct shockwave_data{
    
    int k;
    int N;
    F **encoded_matrix =  nullptr,**matrix =  nullptr;
    vector<vector<_hash>> MT;
    shockwave_data(){
        encoded_matrix = nullptr;
        matrix =  nullptr;
    }
    ~shockwave_data(){
      
        if(k > 0){
            for(int i = 0; i < k; i ++){
                delete[] encoded_matrix[i];
                delete[] matrix[i];
            }
            delete[] encoded_matrix;
            delete[] matrix;
        
        }
        
    }
};

struct Whir_data{
    int k;
    vector<F> poly;
    vector<F> poly_com;
    vector<vector<_hash>> MT;
    vector<vector<vector<_hash>>> FRI_MT;
    vector<vector<F>> FRI_poly;

};

struct PC_data{
    int k;
    vector<F> poly;
    vector<vector<F>> poly_com;
    vector<F> aggr_poly_com;
    vector<F> aggr_poly;
    
    vector<vector<__hhash_digest>> MT;
    vector<vector<__hhash_digest>> aggr_MT;
    
    vector<vector<vector<__hhash_digest>>> FRI_MT;
    vector<vector<F>> FRI_poly;
};

typedef struct MT_proof;
typedef struct FRI_proof;
typedef struct Virgo_proof;
typedef struct PC_data;
typedef struct Whir_data;
typedef struct shockwave_data;

void FRI_commit(vector<F> &poly, PC_data &data);
void Virgo_commit(vector<F> &poly, vector<F> &encoded_poly, vector<vector<__hhash_digest>> &hash_tree,int partitions);
Virgo_proof Virgo_open(vector<F> &poly,vector<F> &encoded_poly, vector<vector<__hhash_digest>> &hash_tree ,vector<F> r, int partitions);
void MT_commit(vector<F> &elements, vector<vector<__hhash_digest>> &hashes, int partitions);
MT_proof MT_Open(size_t idx, vector<vector<__hhash_digest>> &hashes);
void MT_verify(MT_proof P, vector<F> elements, size_t idx);
void fri_prove(PC_data &data, vector<F> x);
void whir_prove(PC_data &data, vector<F> x, double &vt, double &ps);
void change_form(vector<F> &poly, int logn, int l,int pos);
void _whir_prove(Whir_data &data, vector<F> x, double &vt, double &ps);
void whir_commit(vector<F> &poly, Whir_data &data);
F fold(int i, vector<F> arr,vector<F> a, int N, int k);
void shockwave_prove(shockwave_data *data, vector<F> x, double &vt, double &ps);
shockwave_data* shockwave_commit(vector<F> &poly, int k);