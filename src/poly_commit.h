#include "config_pc.hpp"
#include "merkle_tree.h"
#include "Virgo.h"

struct commitment{
	vector<vector<__hhash_digest>> hashes_sha;
	vector<vector<F>> hashes_f;
};


struct aggregation_witness{
	vector<vector<unsigned int>> merkle_proof;
	vector<F> merkle_proof_f;
	vector<F> idx;
	vector<F> idx_f;
	vector<F> root;
	vector<vector<F>> root_sha;
	vector<vector<F>> output;
	vector<F> a;
	int trees,proof_size;  
};


struct Pigeon_breakdown_pp{
};

struct poly_proof{
	F r,y;
	vector<F> tensor,challenge_vector;
	vector<vector<F>> collumns;
	vector<MT_proof> P;
	vector<vector<F>> query_points;
	Virgo_proof P_open;
    vector<MT_proof> paths;
};

typedef struct Pigeon_breakdown_pp;
typedef struct aggregation_witness aggregation_witness;
typedef struct commitment commitment;
typedef struct poly_proof poly_proof;


//vector<vector<unsigned int>> query(int col, int row,  vector<vector<F>> &matrix, __hhash_digest *mt);


vector<vector<F>> naive_breakdown_commit(vector<F> poly, __hhash_digest &comm, vector<__hhash_digest> &leaves);
poly_proof naive_breakdown_open(vector<F> &poly, vector<vector<F>> &encoded_matrix, vector<F> x);
void naive_breakdown_verify(poly_proof P, vector<F> x);
void test_naive_brakedown(unsigned long long int size);
vector<vector<F>> Pigeon_breakdown_commit(vector<F> poly , __hhash_digest &comm, vector<__hhash_digest> &leaves);
void Pigeon_breakdown_gen(Pigeon_breakdown_pp &pp);
poly_proof Pigeon_breakdown_open(vector<F> &poly , vector<vector<F>> &encoded_matrix, vector<F> x);
void test_FFT_brakedown(unsigned long long int size);
void test_pigeon(size_t size, int r_size);
void test_pigeon_stream(int size, int r_size);
void Pigeon_breakdown_commit_stream(stream_descriptor fd , __hhash_digest &comm, vector<vector<__hhash_digest>> &MT_hashes);
poly_proof Pigeon_breakdown_open_stream(stream_descriptor fd, vector<F> x);
vector<double> pigeon_brakedown_verify(poly_proof P);