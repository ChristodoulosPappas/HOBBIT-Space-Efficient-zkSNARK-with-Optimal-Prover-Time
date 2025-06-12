#pragma once
#include "config_pc.hpp"
#include "polynomial.h"
#include "witness_stream.h"



struct mul_tree_proof{
	F initial_randomness;
	// If we have a single product
	size_t size;
	F in1,in2;
	F out_eval;
	vector<struct proof> proofs;
	vector<F> output;
	vector<F> final_r;
	vector<F> global_randomness,individual_randomness;
	vector<F> partial_eval;
	F final_eval;
};
struct proof{
	int type;
	vector<vector<F>> randomness;
	vector<quadratic_poly> q_poly;
	vector<cubic_poly> c_poly;
	vector<F> output;
	vector<F> vr;
	vector<F> gr;
	vector<F> liu_sum;
	vector<vector<F>> sig;
	vector<vector<F>> final_claims_v;
	F divident,divisor,quotient,remainder;
	// Witnesses to make hash calclulation circuit less deep
	vector<vector<vector<F>>> w_hashes;
	vector<F> r,individual_sums;
	vector<vector<F>> Partial_sums;
	vector<quadratic_poly> q_poly1;
	vector<quadratic_poly> q_poly2;
	F final_rand;
	F final_sum;
	int K;

};

struct encoding_proof{
	proof P1,P2,P3;
};

struct encoding_transcript{
    vector<vector<F>> x1;
    vector<vector<F>> x2;
	vector<vector<F>> x2_inp;
};

struct encoding_transcript;
typedef struct proof;
typedef struct encoding_proof;

typedef struct partition_sumcheck1_proof partition_sumcheck1_proof;
typedef struct partition_sumcheck2_proof partition_sumcheck2_proof;
typedef struct partition_sumcheck3_proof partition_sumcheck3_proof;
typedef struct leaves_sumcheck_proof leaves_sumcheck_proof;
typedef struct gini_sumcheck1_proof gini_sumcheck1_proof;
typedef struct gini_sumcheck2_proof gini_sumcheck2_proof;


struct proof prove_fft_matrix(vector<vector<F>> M, vector<F> r, F previous_sum, double &vt, double &ps);
struct proof prove_ifft_matrix(vector<vector<F>> M, vector<F> r, F previous_sum, double &vt, double &ps);
struct proof generate_2product_sumcheck_proof_disk(int fp1, int fp2,int size, F previous_r);

struct proof generate_2product_sumcheck_proof(vector<F> &_v1, vector<F> &_v2, F previous_r, double &vt, double &ps);
int generate_encoding_transcript(encoding_transcript &transcript ,const F *src, F *dst, long long n, int dep, double &vt, double &ps);
//encoding_proof prove_linear_code(vector<F> &arr, encoding_transcript &transcript, int n);
proof prove_linear_code(vector<F> &codeword, int n, double &vt, double &ps);
proof prove_membership(vector<F> &aggr_arr, vector<F> &encoded_arr, double &vt, double &ps);
struct proof _generate_3product_sumcheck_proof(vector<F> &v1, vector<F> &v2, vector<F> &v3,F previous_r, double &vt, double &ps);
//struct proof _generate_3product_sumcheck_proof(vector<F> &v1, vector<F> &v2, vector<F> &v3,F previous_r);
int evaluate_parity_matrix(vector<F> &A, vector<F> &beta1, int Offset, int n, int dep, int &lvl);
void open_parity_matrix(vector<F> r1, vector<F> r2, int n, double &vt, double &ps);
void commit_parity_matrix(int n);
struct proof prove_fft(vector<F> &m, vector<F> r, F previous_sum, double &vt, double &ps);
void generate_3product_sumcheck_beta_stream(stream_descriptor fd1, stream_descriptor fd2, vector<F> r, double &vt, double &ps);
void prove_gate_consistency(stream_descriptor tr, vector<F> r, double &vt, double &ps);
void generate_3product_sumcheck_beta_stream_batch(stream_descriptor fd, vector<vector<F>> r, int batches, int distance, int layer_id,
		vector<F> old_claims, vector<F> &new_claims, vector<vector<F>> &new_r, double &vt, double &ps);

vector<F> prove_multiplication_tree_stream_shallow(stream_descriptor fd,int vectors,int size, F previous_r, int distance, vector<F> prev_x, bool naive,
  double &vt, double &ps);

void prove_gate_consistency_standard(vector<F> &arr_L,vector<F> &arr_R,vector<F> &arr_O,
					vector<F> &add_gate,vector<F> r, double &vt, double &ps);

mul_tree_proof prove_multiplication_tree_new(vector<vector<F>> &input, F previous_r, vector<F> prev_x, double &vt, double &ps);
proof prove_linear_code_batch( vector<vector<F>> &codewords, int n, double &vt, double &ps);
void prove_gate_consistency_lookups(stream_descriptor tr, vector<F> r, double &vt, double &ps);