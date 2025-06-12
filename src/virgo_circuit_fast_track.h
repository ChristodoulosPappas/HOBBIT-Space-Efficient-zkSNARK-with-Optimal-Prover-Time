#pragma once
#ifndef __circuit
#define __circuit
#include <utility>
#include "virgo_prime_field.h"
#include <unordered_map>
#include <vector>

class _gate
{
public:
	int ty;
	long long u, v;
	int *src;
	prime_field::field_element *weight;
	int parameter_length;
	_gate()
	{
		ty = 2;
		u = v = 0;
		src = NULL;
		weight = NULL;
		parameter_length = 0;
	}
	_gate(int t, long long U, long long V)
	{
		ty = t, u = U, v = V;
	}
};

class _layer
{
public:
	int *src_expander_C_mempool, *src_expander_D_mempool;
	prime_field::field_element *weight_expander_C_mempool, *weight_expander_D_mempool;
	_gate *gates;
	int bit_length;
	std::unordered_map<int, std::vector<std::pair<int, std::pair<int, int> > > > u_gates;
	std::unordered_map<int, std::vector<std::pair<int, std::pair<int, int> > > > v_gates;
	bool is_parallel;
	int block_size;
	int log_block_size;
	int repeat_num;
	int log_repeat_num;
	_layer()
	{
		is_parallel = false;
		gates = NULL;
		src_expander_C_mempool = NULL;
		src_expander_D_mempool = NULL;
		weight_expander_C_mempool = NULL;
		weight_expander_D_mempool = NULL;
		bit_length = 0;
	}
	~_layer()
	{
		delete[] gates;
		if(src_expander_C_mempool != NULL)
			delete[] src_expander_C_mempool;
		if(src_expander_D_mempool != NULL)
			delete[] src_expander_D_mempool;
		if(weight_expander_C_mempool != NULL)
			delete[] weight_expander_C_mempool;
		if(weight_expander_D_mempool != NULL)
			delete[] weight_expander_D_mempool;
	}
};

class _layered_circuit
{
public:
	_layer *circuit;
	int total_depth;
	prime_field::field_element *inputs;
	_layered_circuit()
	{
		circuit = NULL;
		total_depth = 0;
		inputs = NULL;
	}
	~_layered_circuit()
	{
		delete[] inputs;
		delete[] circuit;
	}
};

#endif
