#include "config_pc.hpp"
#include "utils.hpp"
#include <vector>
#include "merkle_tree.h"
#include "linear_code_encode.h"

extern int tensor_row_size;

extern size_t BUFFER_SPACE;

void open_standard(vector<F> &poly , vector<F> x,  vector<vector<_hash>> &Commitment_MT,vector<vector<vector<F>>> &_tensor ,int K, double &vt,double &ps);
void commit_standard(vector<F> &poly, _hash &comm, vector<vector<_hash>> &MT_hashes, vector<vector<vector<F>>> &_tensor, int K);
void commit_standard_orion(vector<F> &poly, _hash &comm, vector<vector<_hash>> &MT_hashes);
void open_orion_standard(vector<F> &poly , vector<F> x,  vector<vector<_hash>> &Commitment_MT);
void test_PC(size_t N, int option, int K);
void test_tensorcodes(size_t N, int option);