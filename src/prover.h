#pragma once

#include "circuit.h"
#include <vector>
#include <ctime>
#include <algorithm>
#include <memory>
#include "config_pc.hpp"
#include "polynomial.h"
#include "mimc.h"
#include "GKR.h"
#include "sumcheck.h"

using std::unique_ptr;



struct recursion_proof{
};
typedef struct recursion_proof recursion_proof; 

struct proof_stream{
	F sum,new_sum;
    int c,size;
	vector<F> transcript;
    vector<vector<F>> polynomials;
    recursion_proof RP;
	vector<F> randomness;
	vector<proof> P;
	vector<F> vr;
	vector<F> _a;

};


typedef struct proof_stream proof_stream; 

void prove_circuit(F commitment);
void prove_circuit_standard(F commitment);