
#include "config_pc.hpp"
#include "virgo_poly_commit.h"
#include <unistd.h>
#include <math.h>

prime_field::field_element *_q_eval_real;
prime_field::field_element *_q_eval_verifier;
prime_field::field_element *_q_ratio;
poly_commit::poly_commit_prover p;
    

extern double commit_timer;

void _dfs_for_public_eval(int dep, prime_field::field_element val, prime_field::field_element *r_0, prime_field::field_element *one_minus_r_0, int r_0_len, int pos)
{
	if(dep == r_0_len)
		_q_eval_real[pos] = val;
	else
	{
		_dfs_for_public_eval(dep + 1, val * one_minus_r_0[r_0_len - 1 - dep], r_0, one_minus_r_0, r_0_len, pos << 1);
		_dfs_for_public_eval(dep + 1, val * r_0[r_0_len - 1 - dep], r_0, one_minus_r_0, r_0_len, pos << 1 | 1);
	}
}

void _dfs_ratio(int dep, prime_field::field_element val, prime_field::field_element *r, prime_field::field_element *one_minus_r, int pos)
{
    if(dep == log_slice_number)
        _q_ratio[pos] = val;
    else
    {
        _dfs_ratio(dep + 1, val * one_minus_r[log_slice_number - 1 - dep], r, one_minus_r, pos << 1);
		_dfs_ratio(dep + 1, val * r[log_slice_number - 1 - dep], r, one_minus_r, pos << 1 | 1);
    }
}

void _dfs_coef(int dep, prime_field::field_element val, prime_field::field_element *r, prime_field::field_element *one_minus_r, int pos, int r_len)
{
    if(dep == r_len)
        _q_eval_verifier[pos] = val;
    else
    {
        _dfs_coef(dep + 1, val * one_minus_r[r_len - 1 - dep], r, one_minus_r, pos << 1, r_len);
		_dfs_coef(dep + 1, val * r[r_len - 1 - dep], r, one_minus_r, pos << 1 | 1, r_len);
    }
}
prime_field::field_element* _public_array_prepare_generic(prime_field::field_element *public_array, int log_length)
{
	prime_field::field_element *q_coef_arr = new prime_field::field_element[1 << log_length];
	int coef_slice_size = (1 << (log_length - log_slice_number));
	for(int i = 0; i < (1 << log_slice_number); ++i)
	{
		inverse_fast_fourier_transform(&public_array[i * coef_slice_size], coef_slice_size, coef_slice_size, prime_field::get_root_of_unity(log_length - log_slice_number), &q_coef_arr[i * coef_slice_size]);
	}
	return q_coef_arr;
}

prime_field::field_element* _public_array_prepare(prime_field::field_element *r, prime_field::field_element *one_minus_r, int log_length, prime_field::field_element *_q_eval_real)
{
	_q_eval_verifier = new prime_field::field_element[(1 << (log_length - log_slice_number))];
    _q_ratio = new prime_field::field_element[(1 << log_slice_number)];
    _dfs_ratio(0, prime_field::field_element(1), r + log_length - log_slice_number, one_minus_r + log_length - log_slice_number, 0);
    _dfs_coef(0, prime_field::field_element(1), r, one_minus_r, 0, log_length - log_slice_number);
    prime_field::field_element *q_coef_verifier = new prime_field::field_element[(1 << (log_length - log_slice_number))];
    inverse_fast_fourier_transform(_q_eval_verifier, (1 << (log_length - log_slice_number)), (1 << (log_length - log_slice_number)), prime_field::get_root_of_unity(log_length - log_slice_number), q_coef_verifier);
	
	prime_field::field_element *q_coef_arr = new prime_field::field_element[1 << log_length];
	int coef_slice_size = (1 << (log_length - log_slice_number));
	for(int i = 0; i < (1 << log_slice_number); ++i)
	{
		for(int j = 0; j < coef_slice_size; ++j)
		{
			q_coef_arr[i * coef_slice_size + j] = q_coef_verifier[j] * _q_ratio[i];
			assert(_q_eval_real[i * coef_slice_size + j] == _q_ratio[i] * _q_eval_verifier[j]);
		}
	}
	delete[] q_coef_verifier;
	delete[] _q_eval_verifier;
	delete[] _q_ratio;
	return q_coef_arr;
}

__hhash_digest virgo_commit(vector<F> &poly){
    int N = 1 << (int)log2(poly.size());
    prime_field::field_element *coefs = new prime_field::field_element[N];
    for(int i = 0; i < N; ++i){
        coefs[i].real = poly[i].real;
        coefs[i].img = poly[i].img;
    }
    return p.commit_private_array(coefs, log2(poly.size()));
	
}

void virgo_open(vector<F> &poly, vector<F> x, __hhash_digest C, double &vt, double &ps){
    int N = 1ULL<<(x.size());
    int lg_N = x.size();
    prime_field::field_element *output = new prime_field::field_element[N];
    prime_field::field_element *mask = new prime_field::field_element[1];
    prime_field::field_element one = prime_field::field_element(1);
    mask[0] = prime_field::field_element(0);
    
    prime_field::field_element *processed = new prime_field::field_element[lg_N];
    
    for (int i = 0; i < lg_N; ++i)
    {
        processed[i].real = poly[i].real;
        processed[i].img = poly[i].img;
        
    }

    prime_field::field_element *r = new prime_field::field_element[lg_N];
    prime_field::field_element *one_minus_r_0 = new prime_field::field_element[lg_N];
    
    for(int  i= 0; i < lg_N; i++){
        r[i].real = x[i].real;
        r[i].img = x[i].img;
        one_minus_r_0[i] = one - r[i];
    }
    
    _q_eval_real = new prime_field::field_element[N];
    for(int i = 0; i < N; i++){
        _q_eval_real[i] = prime_field::field_element(i);
    }
    
    
	_dfs_for_public_eval(0, prime_field::field_element(1), r, one_minus_r_0, lg_N, 0);
	prime_field::field_element *all_sum =  new prime_field::field_element[slice_number];
    prime_field::field_element alpha_beta_sum = prime_field::field_element(1);
    
	
	auto merkle_root_h = (p).commit_public_array(_q_eval_real, lg_N, alpha_beta_sum, all_sum);
	
	
	prime_field::field_element *public_array = _public_array_prepare(r, one_minus_r_0, lg_N, _q_eval_real);
	
    prime_field::field_element input_0;
    
    double commit_pt = 0.0, commit_vt = 0.0;
    int commit_ps = 0;
    poly_commit::poly_commit_verifier v;
    v.p = &p;
  
	bool flag = v.verify_poly_commitment(all_sum, lg_N, public_array, commit_vt, commit_ps, commit_pt, C, merkle_root_h);
  	vt += commit_vt;
	ps += commit_ps/1024.0;
	
	//delete[] _q_eval_real;
	//delete[] _q_eval_verifier;
	//delete[] _q_ratio;
	//_q_eval_real = NULL;
	//_q_eval_verifier = NULL;
	//_q_ratio = NULL;
    /*
    for(int i = 0; i < 2; i++){
		//delete[] fri::witness_merkle[i];
		//delete[] fri::witness_rs_codeword_interleaved[i];
		//delete[] fri::visited_init[i];
		//delete[] fri::visited_witness[i];
		//delete[] fri::leaf_hash[i];
		fri::witness_merkle[i] = NULL;
		fri::witness_rs_codeword_interleaved[i] = NULL;
		fri::visited_init[i] = NULL;
		fri::visited_witness[i] = NULL;
		fri::leaf_hash[i] = NULL;
	}
	for(int i = 0; i < 2; i++){
		for(int j = 0; j < slice_number; j++){
			//delete[] fri::witness_rs_codeword_before_arrange[i][j];
			//delete[] fri::witness_rs_mapping[i][j];
			fri::witness_rs_codeword_before_arrange[i][j] = NULL;
			fri::witness_rs_mapping[i][j] = NULL;
		}
	}
	for(int i = 0; i < max_bit_length; i++){
		//delete fri::visited[i];
		fri::visited[i] = NULL;
	}
	fri::L_group = NULL;
	fri::r_extended = NULL;
	fri::virtual_oracle_witness = NULL;
	fri::virtual_oracle_witness_mapping = NULL;
	*/
    fri::delete_self();
	//delete[] fri::L_group;
	//delete[] fri::r_extended;
	//delete[] fri::virtual_oracle_witness;
	//delete[] fri::virtual_oracle_witness_mapping;
	
}
