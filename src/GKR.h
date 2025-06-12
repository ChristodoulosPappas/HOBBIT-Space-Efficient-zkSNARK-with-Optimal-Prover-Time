#pragma once
#include "inputCircuit.hpp"
#include <gmp.h>
#include <stdlib.h>
#include "polynomial.h"
#include "config_pc.hpp"
#include <map>
//#include "sumcheck.h"

#define GKR_PROOF 1
#define RANGE_PROOF 2
#define RANGE_PROOF_OPT 6
#define RANGE_PROOF_LOOKUP 7

#define MATMUL_PROOF 3 
#define ADD_PROOF 4
#define DIVISION_CHECK 5



int test_gkr(vector<F> data, vector<F> randomness, int N, int M, int layers);
void test_m2m(vector<F> data, vector<F> randomness, int cols, int rows, int circuits);
int test_sha256(vector<F> data, vector<F> randomness, int hashes);
int test_multree(vector<F> data, vector<F> randomness, int N, int M, int layers);
int test_gkr_standard(int N, int M, int layers);