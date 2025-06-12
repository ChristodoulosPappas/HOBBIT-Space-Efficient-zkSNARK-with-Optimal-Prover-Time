//
// Created by 69029 on 6/23/2021.
//
#pragma once

#include "my_hhash.h"
#include "config_pc.hpp"
#include "witness_stream.h"

extern double proving_time;
F chain_hash(F previous_r, vector<F> values);
vector<F> generate_randomness(int size, F seed);
void precompute_beta(vector<F> r,vector<F> &B);
void pad_vector(vector<F> &v);
float proof_size(vector<struct proof> P);
vector<vector<F>> generate_tables();
vector<F> lookup_prod(vector<vector<F>> tables, F num);
vector<F> generate_randomness(int size);
vector<vector<F>> get_poly(int size);
vector<F> get_predicates(int size);
F lookup(vector<vector<F>> tables, F num);
F evaluate_matrix(vector<vector<F>> M, vector<F> r1, vector<F> r2);
F evaluate_vector(vector<F> v,vector<F> r);
vector<F> prepare_matrix(vector<vector<F>> M, vector<F> r);
vector<F> convert2vector(vector<vector<F>> M);
void write_data(vector<F> data,char *filename);
vector<F> tensor2vector(vector<vector<vector<vector<F>>>> M);
vector<vector<vector<vector<F>>>> vector2tensor(vector<F> v,vector<vector<vector<vector<F>>>> M,int w);
vector<vector<F>> transpose(vector<vector<F>> M);
vector<vector<F>> convert2matrix(vector<F> arr, int d1, int d2);
vector<F> prepare_bit_vector(vector<F> num, int domain);
vector<vector<F>> rotate(vector<vector<F>> M);
void initBetaTable(vector<F> &beta_g, u8 gLength, const vector<F>::const_iterator &r, const F &init);

void
initBetaTable(vector<F> &beta_g, int gLength, const vector<F>::const_iterator &r_0,
              const vector<F>::const_iterator &r_1, const F &alpha, const F &beta);

void fft(vector<F> &arr, int logn, bool flag);
//F getRootOfUnit(int n);
void phiGInit(vector<F> &phi_g, const vector<F>::const_iterator &rx, const F &scale, int n, bool isIFFT);
template <class T>
void myResize(vector<T> &vec, u64 sz) {
    if (vec.size() < sz) vec.resize(sz);
}

void compute_binary(vector<F> r, vector<F> &B);
F getRootOfUnity(int n);

void get_field_vector(vector<F> &h_f, vector<__hhash_digest> &h);
vector<F> compute_lagrange_coeff(F omega, F r, int degree);

void my_fft(vector<F> &arr, vector<F> &w, vector<u32> &rev, F ilen,  bool flag);
void compute_convolution(vector<vector<F>> Lv, vector<F> &B);
vector<F> evaluate_vector_stream_batch(stream_descriptor fp,vector<vector<F>> r, size_t size);
F evaluate_vector_stream(stream_descriptor fp, vector<F> r, size_t size);
void _fft(F *arr, int logn, bool flag);

void init_matrix(F **&M, int rows, int cols);
void free_matrix(F **M,int rows);
F * init_vector( int rows);
void free_vector(F *M);
void __fft(F *&arr,  int logn, bool flag);