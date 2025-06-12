#pragma once
#include "verifier_standard.h"
#include "inputCircuit.hpp"
#include "circuit.h"
#include "sumcheck.h"
//#include <gmp.h>
#include <stdlib.h>
#include "polynomial.h"
#include "config_pc.hpp"
#include <map>

#define GKR_PROOF 1
#define RANGE_PROOF 2
#define RANGE_PROOF_OPT 6
#define RANGE_PROOF_LOOKUP 7
#define MATMUL_PROOF 3 
#define ADD_PROOF 4
#define DIVISION_CHECK 5
#define LOOKUP_PROOF 8
#define HASH_SUMCHECK 9

struct layer_proof{
	int type;
	vector<F> output;
	F initial_randomness,out_eval;
	vector<vector<F>> randomness;
	vector<quadratic_poly> q_poly;
	vector<cubic_poly> c_poly;	
	vector<F> vr;
	vector<vector<vector<F>>> w_hashes;
	
	F final_rand;
};

typedef struct layer_proof layer_proof;


struct lookup_proof{
	F previous_r;
	proof mP1,mP2;
	proof sP1;
	vector<F> mul_out1,mul_out2,read_eval_x,write_eval_x,indexes_eval,x1;
	F read_eval,read_eval1,read_eval2,write_eval,write_eval1,write_eval2,sum1,sum2;
	F final_eval;
	F final_rand;

};


struct polynomial_data{
	vector<F> poly;
	vector<vector<F>> eval_point;
	vector<F> eval;
};

struct feedforward_proof{
	map<string,struct polynomial_data> poly_map;
	vector<struct proof> proofs;
};

struct SHA_witness{
	vector<F> bits;
	vector<F> aux,numbers;
};

typedef struct SHA_witness SHA_witness;
typedef struct Point Point;

struct proof prove_matrix_evaluations(vector<F> &data, vector<F> randomness,   int sizes, int b1_size,int b2_size, int read_write_size);