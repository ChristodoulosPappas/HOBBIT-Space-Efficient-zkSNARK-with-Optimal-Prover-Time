#include "config_pc.hpp"
#include "utils.hpp"
#include <vector>
#include "merkle_tree.h"
#include "linear_code_encode.h"
#include <omp.h>

extern int tensor_row_size;

extern size_t BUFFER_SPACE;

void commit(stream_descriptor fd , _hash &comm, vector<vector<_hash>> &MT_hashes);

void open(stream_descriptor fd , vector<F> x,  vector<vector<_hash>> &Commitment_MT, double &vt, double &ps);
void init_commitment(bool mod);
void test_Elastic_PC(size_t N, int option);