#include "sumcheck.h"
#include "virgo_PC.h"
#include "utils.hpp"
#include "linear_code_encode.h"

void compute_tensorcode(vector<F> &message, vector<vector<F>> &tensor);
void recursive_prover_Spielman(vector<F> &input,vector<vector<F>> &C, vector<size_t> I,double &vt , double &ps);
void recursive_prover_RS(vector<F> &aggregated_vector, vector<vector<size_t>> I,double &vt, double &ps );
void _compute_tensorcode(F *message, F **tensor, int N);
void recursive_prover_brakingbase(vector<F> &codeword, vector<size_t> I, double &vt, double &ps);
void recursive_prover_orion(vector<vector<F>> &codewords, double &vt,double &ps);
void recursive_prover_Spielman_stream(vector<F> &input,vector<vector<F>> &M,vector<vector<F>> &codewords , vector<vector<size_t>> I,double &vt , double &ps);