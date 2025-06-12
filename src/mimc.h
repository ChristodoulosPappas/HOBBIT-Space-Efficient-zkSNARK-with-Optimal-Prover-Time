#pragma once

#include "config_pc.hpp"

void init_hash();
F mimc_hash(F input, F k);
F mimc_multihash(vector<F> input);
vector<F> mimc_multihash2(vector<F> input);
vector<vector<F>> mimc_multihash3(vector<F> input);
vector<F> mimc_hash_segments(F input, F k);
vector<F> get_parameters();