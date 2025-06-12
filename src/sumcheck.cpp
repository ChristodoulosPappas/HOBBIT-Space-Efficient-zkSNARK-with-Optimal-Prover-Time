#include "config_pc.hpp"
#include <math.h>
#include "utils.hpp"
#include "sumcheck.h"
#include "mimc.h"
#include <chrono>
#include "expanders.h"
#include "GKR_standard.h"
#include "Virgo.h"
#include "Elastic_PC.hpp"
#include <unistd.h>

using namespace std::chrono;

extern int threads;
extern int bin_size;
extern double range_proof_verification_time;
extern int range_proof_size;
extern size_t MAX_CHUNCK;
extern size_t BUFFER_SPACE;
extern size_t BUFFER_SPACE_tr;
extern int _WRITE;
extern string dir;
F *scratch_proof[2][100];
unsigned long int scratch_size_proof[100];
bool __encode_initialized_proof = false;
double sc_vt = 0.0;
shockwave_data *C_p;
double routine_time = 0.0;
extern vector<F> lookup_rand;
extern bool has_lookups;

// takes as input vectors x of equal size and for each 
// vector outputs Prod_i = x[0]*x[1]*x[2]...x[N]
mul_tree_proof prove_multiplication_tree_new(vector<vector<F>> &input, F previous_r, vector<F> prev_x, double &vt, double &ps){
	int vectors = input.size();
	
	int depth = (int)log2(input[0].size());
	int size = input[0].size();
	for(int i = 0; i < input.size(); i++){
		if(input[i].size() != size){
			printf("Error in mul tree sumcheck, no equal size vectors\n");
			exit(-1);
		}
	}

	if(1<<depth != size){
		depth++;
		size = 1<<depth;
		for(int i = 0; i < input.size(); i++){
			input[i].resize(1<<depth,F(1));
		}
	}

	if(vectors != 1<<((int)log2(vectors))){
		vectors = 1<<((int)log2(vectors)+1);
		int old_vector_size = input.size();
		vector<F> temp_vector(1<<depth,F(0));
		for(int i = 0; i < vectors-old_vector_size; i++){
			input.push_back(temp_vector);
		}
	}
	
	// Initialize total input
	int total_input_size = vectors*size;
	
	//printf("total input %d\n",total_input_size );
	vector<F> total_input(total_input_size);
	int counter = 0;
	for(int j = 0; j < input.size(); j++){
		for(int i = 0; i < input[0].size(); i++){
			total_input[counter] = input[j][i];
			counter++;
		}
	}	
	

	vector<vector<F>> transcript(depth);
	vector<vector<F>> in1(depth),in2(depth);
	for(int i = 0; i < depth; i++){
		transcript[i].resize(total_input_size/(1<<(i+1)));
		in1[i].resize(total_input_size/(1<<(i+1)));
		in2[i].resize(total_input_size/(1<<(i+1)));
	}
	
	counter = 0;
	for(int i = 0; i < total_input_size/2; i++){
		transcript[0][counter] = total_input[2*i]*total_input[2*i+1];
		in1[0][counter] = total_input[2*i];
		in2[0][counter] = total_input[2*i+1];
		counter++;
		
	}
	int len = total_input_size/2;
	for(int i = 1; i < transcript.size(); i++){
		counter = 0;
		for(int j = 0; j < len/2; j++){
			transcript[i][counter] = transcript[i-1][2*j]*transcript[i-1][2*j + 1];
			in1[i][counter] = transcript[i-1][2*j];
			in2[i][counter] = transcript[i-1][2*j + 1];
			counter++;
		}
		
		len = len/2;
	}
	

	//printf("Final prod len : %d\n",transcript[depth-1].size());
	proof P;
	mul_tree_proof Proof;
	Proof.size = size;
	if(transcript[transcript.size()-1].size() == 1){
		Proof.initial_randomness = previous_r;
		vector<F> r;
		previous_r = mimc_hash(previous_r,transcript[transcript.size()-1][0]);
		Proof.output =transcript[transcript.size()-1];

		F sum = transcript[transcript.size()-1][0];
		Proof.out_eval = sum;
		clock_t s,e;
		s = clock();
		for(int i = depth-1; i >= 0; i--){
			vector<F> beta;
			if(r.size() == 0){
				Proof.in1 = in1[i][0];
				Proof.in2 = in2[i][0];
				F num = mimc_hash(previous_r,in1[i][0]);
				previous_r = mimc_hash(num,in2[i][0]);		
				sum = (F(1)-previous_r)*in1[i][0]+(previous_r)*in2[i][0];
				r.push_back(previous_r);	
			}else{
				precompute_beta(r,beta);
				P = _generate_3product_sumcheck_proof(in1[i], in2[i],beta,  previous_r,vt,ps);
				
				Proof.proofs.push_back(P);
				if(sum != P.c_poly[0].eval(F(1)) +  P.c_poly[0].eval(F(0))){
					printf("error %d\n",i );
				}
				r = P.randomness[0];
				
				//previous_r = generate_randomness(1,r[r.size()-1])[0];
				previous_r = P.final_rand;
				//previous_r = mimc_hash(P.final_rand,P.vr[0]);
				//previous_r = mimc_hash(previous_r,P.vr[1]);
				
				sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
				beta.clear();
				r.insert(r.begin(),previous_r);
			}
			//sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
		}
		e = clock();
		
		Proof.final_r = r;
		Proof.final_eval = sum;
		vector<F> individual_randomness;
		vector<F> global_randomness;
		
		for(int i = 0; i < (int)log2(size); i++){
			individual_randomness.push_back(r[r.size()-(int)log2(size)+i]);
		}
		Proof.individual_randomness = individual_randomness;
		for(int i = 0; i < r.size()-(int)log2(size); i++){
			global_randomness.push_back(r[i]);
		}
		Proof.global_randomness = global_randomness;
		
	}else{
		Proof.initial_randomness = previous_r;
		Proof.output = transcript[depth-1];
		vector<F> r;
		if(prev_x.size() == 0){
			r = generate_randomness((int)log2(transcript[depth-1].size())); 	
		}else{
			r = prev_x;
		}
		
		F sum = evaluate_vector(transcript[depth-1],r);
		Proof.out_eval = sum;
		proof P;
		vector<F> beta;
		if(prev_x.size() == 0){
			previous_r = mimc_hash(r[r.size()-1],sum);
		}
		clock_t s,e;
		s = clock();
		precompute_beta(r,beta);
		for(int i = depth-1; i >= 0; i--){
			vector<F> beta;
			precompute_beta(r,beta);
			vector<F> t;
			
			P = _generate_3product_sumcheck_proof(in1[i], in2[i],beta,  previous_r, vt,ps);

			Proof.proofs.push_back(P);
			if(sum != P.c_poly[0].eval(F(1)) +  P.c_poly[0].eval(F(0))){
				printf("error %d\n",i );
			}
			r = P.randomness[0];
			
			previous_r = P.final_rand;
			
			//previous_r = mimc_hash(P.final_rand,P.vr[0]);
			//previous_r = mimc_hash(previous_r,P.vr[1]);
				
			sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
			beta.clear();
			r.insert(r.begin(),previous_r);
		}
		e = clock();
		
		// Correctness verification
		if(evaluate_vector(total_input,r) != sum){
			printf("Error in mul tree final\n");
			exit(-1);
		}
		// Check individual input evaluation
		Proof.final_r = r;
		Proof.final_eval = sum;
		vector<F> individual_randomness;
		vector<F> global_randomness;
		
		for(int i = 0; i < (int)log2(size); i++){
			individual_randomness.push_back(r[i]);
		}
		Proof.individual_randomness = individual_randomness;
		for(int i = 0; i < r.size()-(int)log2(size); i++){
			global_randomness.push_back(r[i+(int)log2(size)]);
		}
		Proof.global_randomness = global_randomness;
		vector<F> partial_eval(input.size());
		for(int i = 0; i < partial_eval.size(); i++){
			partial_eval[i] = evaluate_vector(input[i],individual_randomness);
		}
		Proof.partial_eval = partial_eval;
		if(sum != evaluate_vector(partial_eval,global_randomness)){
			printf("Error in mul tree peval\n");
			exit(-1);
		}

		vector<F> muls(input.size(),F(1));
		for(int i = 0; i < input.size(); i++){
			for(int j = 0; j < input[i].size(); j++){
				muls[i] = muls[i]*input[i][j];
			}
		}
		for(int i = 0; i < transcript[depth-1].size(); i++){
			if(transcript[depth-1][i] != muls[i]){
				printf("Error\n");
				exit(-1);
			}
		}

	}
	
	return Proof;
}

/*
vector<vector<F>> prepare_matrixes(vector<vector<F>> M1, vector<vector<F>> M2, vector<F> r1, vector<F> r2){
	vector<vector<F>> V(2);
	vector<vector<F>> M = _transpose(M1);

	V[0] = (prepare_matrix(M,r1));

	M = _transpose(M2);
	
	V[1] = (prepare_matrix(M,r2));
	
	return V;

}
*/

struct proof batch_3product_sumcheck(vector<vector<F>> &arr1, vector<vector<F>> &arr2, vector<vector<F>> &arr3,
		vector<F> a, double &vt, double &ps){
	proof P;
	size_t L = 0;
	F rand = F(312);
	
	for(int i = 0; i < arr1.size(); i++){
		if(L < arr1[i].size()) L = arr1[i].size(); 
	}

	int rounds = (int)log2(L);
	
	vector<cubic_poly> polynomials;
	vector<F> r;
	P.vr.resize(3*a.size(),F(-1));
	for(int i = 0; i < rounds; i++){
		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		for(int j = 0; j < a.size(); j++){		
			cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			cubic_poly p = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3;
			if((int)log2(arr1[j].size()) - 1-i >= 0){
				L = 1 << ((int)log2(arr1[j].size()) - 1-i);
			}else{
				L =  0;
			}
			
			if(L >= 1){		
				for(int k = 0; k < L; k++){
					l1 = linear_poly(arr1[j][2*k+1] - arr1[j][2*k],arr1[j][2*k]);
					l2 = linear_poly(arr2[j][2*k+1] - arr2[j][2*k],arr2[j][2*k]);
					l3 = linear_poly(arr3[j][2*k+1] - arr3[j][2*k],arr3[j][2*k]);
					temp_poly = l1*l2*l3;
					p = p + temp_poly;
				}
		
				
			}else{
				if(P.vr[3*j] == F(-1)){
					P.vr[3*j] = arr1[j][0];
					P.vr[3*j+1] = arr2[j][0];
					P.vr[3*j+2] = arr3[j][0];
				}
				l1 = linear_poly(- arr1[j][0],arr1[j][0]);
				l2 = linear_poly(- arr2[j][0],arr2[j][0]);
				l3 = linear_poly(- arr3[j][0],arr3[j][0]);
				temp_poly = l1*l2*l3;
				p = p + temp_poly;
			}
			p.a = a[j]*p.a;
			p.b = a[j]*p.b;
			p.c = a[j]*p.c;
			p.d = a[j]*p.d;
			poly = poly + p;
		}
		clock_t t1 = clock();
		rand = mimc_hash(rand,poly.a);
		rand = mimc_hash(rand,poly.b);
		rand = mimc_hash(rand,poly.c);
		rand = mimc_hash(rand,poly.d);
		r.push_back(rand);
		polynomials.push_back(poly);
		clock_t t2 = clock();
		vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
		ps += 4*sizeof(F)/1024.0;
		for(int j = 0; j < a.size(); j++){
			if((int)log2(arr1[j].size()) - 1-i >= 0){
				L = 1 << ((int)log2(arr1[j].size()) - 1-i);
			}else{
				L = 0;
			}
			if(L >= 1){
				for(int k = 0; k < L; k++){
					arr1[j][k] = arr1[j][2*k] + rand*(arr1[j][2*k+1]-arr1[j][2*k]);
					arr2[j][k] = arr2[j][2*k] + rand*(arr2[j][2*k+1]-arr2[j][2*k]);
					arr3[j][k] = arr3[j][2*k] + rand*(arr3[j][2*k+1]-arr3[j][2*k]);
				}
			}else{
				arr1[j][0] = (F(1)-rand)*arr1[j][0];
				arr2[j][0] = (F(1)-rand)*arr2[j][0];
				arr3[j][0] = (F(1)-rand)*arr3[j][0];
			}	
		}
		
	}
	for(int i = 0; i < a.size(); i++){
		if(P.vr[3*i] == F(-1)){
			P.vr[3*i] = arr1[i][0];
			P.vr[3*i+1] = arr2[i][0];
			P.vr[3*i+2] = arr3[i][0];
		}
	}
	ps += (P.vr.size()-P.vr.size()/3)*sizeof(F)/1024.0;

	P.randomness.push_back(r);
	P.c_poly = polynomials;
	return P;
}

void compute2p_error_terms(vector<F> &buff1,vector<F> &buff2,vector<F> &fold_buff1, vector<F> &fold_buff2, F &K1, F &K2){
	for(int i = 0; i < buff1.size(); i++){
		K1 += buff1[i]*fold_buff2[i] + buff2[i]*fold_buff1[i];
		K2 += buff1[i]*buff2[i];
	}
}

void compute4p_error_terms(vector<F> &buff1,vector<F> &buff2,vector<F> &buff3, vector<int> &buff4,
	vector<F> &fold_buff1, vector<F> &fold_buff2, vector<F> &fold_buff3, vector<F> &fold_buff4,
	F &K1, F &K2, F &K3, F &K4){
		F gate;
		for(int i = 0; i  < buff1.size(); i++){
			gate = F(1)-buff4[i];
			if(has_lookups){
				if(buff4[i] == 1){
					gate = F(1);
				}else{
					gate = F(0);
				}
			}
			F t1 = fold_buff1[i]*buff2[i] + fold_buff2[i]*buff1[i];
			F t2 = fold_buff3[i]*(gate) + fold_buff4[i]*buff3[i];
			F t3 = buff1[i]*buff2[i];
			F t4 = (gate)*buff3[i];
			F t5 = fold_buff1[i]*fold_buff2[i];
			F t6 = fold_buff3[i]*fold_buff4[i];
			K1 += t1*t6 + t2*t5;
			K2 += t1*t2+t3*t6+t4*t5;
			K3 += t1*t4+t2*t3;
			K4 += t3*t4;
		}
}

void compute3p_error_terms(vector<F> &buff1,vector<int> &buff2,vector<F> &fold_buff1,
	vector<F> &fold_buff2, vector<F> &fold_buff3, vector<F> &beta,F &K1, F &K2, F &K3){
	
	for(int j = 0; j < buff1.size(); j++){
		F gate = F(buff2[j]);
		if(has_lookups){
			gate = F(0);
			if(buff2[j] == 0 && buff2[j] < 4){
				gate = F(1);
			}else if(buff2[j] == 1){
				gate = F(0);
			}else if(buff2[j] == 2){
				gate = lookup_rand[0];
			}else if(buff2[j] == 3){
				gate = lookup_rand[1];
			}else if(buff2[j] == 4){
				gate = F(1);
			}
		}
		F t1 = buff1[j]*fold_buff2[j] + gate*fold_buff1[j];
		F t2 = buff1[j]*gate;
		K1 += fold_buff3[j]*t1 + beta[j]*fold_buff1[j]*fold_buff2[j];
		K2 += beta[j]*t1 + fold_buff3[j]*t2;
		K3 += t2*beta[j];
	}
}

void prove_gate_consistency_standard(vector<F> &arr_L,vector<F> &arr_R,vector<F> &arr_O,
					vector<F> &add_gate,vector<F> r, double &vt, double &ps){
	
	vector<F> beta,mul_gate(add_gate.size());
	for(int i = 0; i  < mul_gate.size(); i++){
		mul_gate[i] = F(1)-add_gate[i];
	}
	precompute_beta(r,beta);
	int L = (int)log2(arr_L.size());
	F rand = F(213);
	F sum = F(0);

	
	for(int i  = 0; i < L; i++){
		cubic_poly poly1 = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		quadruple_poly poly = quadruple_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		quadratic_poly poly2 = quadratic_poly(F_ZERO,F_ZERO,F_ZERO); 
		linear_poly l1,l2,l3,l4;
			
		for(int j = 0; j < (1ULL<<(L-i-1)); j++){
			l1 = linear_poly(add_gate[2*j+1] - add_gate[2*j],add_gate[2*j]);
			l2 = linear_poly(beta[2*j+1] - beta[2*j],beta[2*j]);
			l3 = linear_poly((arr_L[2*j+1] - arr_L[2*j])+(arr_R[2*j+1] - arr_R[2*j]),
			arr_L[2*j]+arr_R[2*j]);
			poly1 = poly1+ (l1*l2*l3);
		}
		for(int j = 0; j < (1ULL<<(L-i-1)); j++){
			l1 = linear_poly(mul_gate[2*j+1] - mul_gate[2*j],mul_gate[2*j]);
			l2 = linear_poly(beta[2*j+1] - beta[2*j],beta[2*j]);
			l3 = linear_poly(arr_L[2*j+1] - arr_L[2*j],arr_L[2*j]);
			l4 = linear_poly(arr_R[2*j+1] - arr_R[2*j],arr_R[2*j]);
			poly = poly + (l1*l2*l3*l4);
		}
		for(int j = 0; j < (1ULL<<(L-i-1)); j++){
			l1 = linear_poly(beta[2*j+1] - beta[2*j],beta[2*j]);
			l2 = linear_poly(arr_O[2*j+1] - arr_O[2*j],arr_O[2*j]);
			poly2 = poly2+ l1*l2;
		}
		poly.a = poly.a;
		poly.b = poly.b + poly1.a;
		poly.c = poly.c + poly1.b - poly2.a;
		poly.d = poly.d + poly1.c - poly2.b;
		poly.e = poly.e + poly1.d - poly2.c;
		rand = mimc_hash(poly.a,rand);
		rand = mimc_hash(poly.b,rand);
		rand = mimc_hash(poly.c,rand);
		rand = mimc_hash(poly.d,rand);
		rand = mimc_hash(poly.e,rand);
		if(sum != poly.eval(F(0)) + poly.eval(F(1))){
			printf("Error in gate consistency 2: %d\n",i);
			//exit(-1);
		}
		sum = poly.eval(rand);
		//sumcheck_rand.push_back(rand);

		for(int j = 0; j < (1ULL<<(L-i-1)); j++){
			add_gate[j] = add_gate[2*j] + rand*(add_gate[2*j+1]-add_gate[2*j]);
			arr_L[j] = arr_L[2*j] + rand*(arr_L[2*j+1]-arr_L[2*j]);
			arr_R[j] = arr_R[2*j] + rand*(arr_R[2*j+1]-arr_R[2*j]);
			arr_O[j] = arr_O[2*j] + rand*(arr_O[2*j+1]-arr_O[2*j]);
			mul_gate[j] = mul_gate[2*j] + rand*(mul_gate[2*j+1]-mul_gate[2*j]);
			beta[j] = beta[2*j] + rand*(beta[2*j+1]-beta[2*j]);
		}
	}
	


}

void prove_gate_consistency_lookups(stream_descriptor tr, vector<F> r, double &vt, double &ps){
	vector<F> fold_L(BUFFER_SPACE),fold_R(BUFFER_SPACE),fold_O(BUFFER_SPACE);
	vector<F> fold_lkp_O(BUFFER_SPACE);
	vector<F> buff_L(BUFFER_SPACE),buff_R(BUFFER_SPACE),buff_O(BUFFER_SPACE);
	vector<F> fold_add_L(BUFFER_SPACE),fold_add_R(BUFFER_SPACE);
	vector<F> fold_mul(BUFFER_SPACE);
	vector<F> fold_lkp(BUFFER_SPACE);
	vector<int> buff_S(BUFFER_SPACE);

	vector<F> r1,beta,fold_beta;
	for(int i = 0; i < (int)log2(BUFFER_SPACE); i++){
		r1.push_back(r[i]);
	}
	precompute_beta(r1,beta);fold_beta = beta;
	
	read_trace(tr,buff_L,buff_R,buff_O,buff_S);
	fold_L = buff_L;
	fold_R = buff_R;
	fold_O = buff_O;
	for(int i = 0; i < BUFFER_SPACE; i++){
		fold_mul[i] = F(0);
		fold_add_L[i] = F(0);
		fold_add_R[i] = F(0);
		fold_lkp[i] = F(0);
		fold_lkp_O[i] = F(0);
		if(buff_S[i] == 0){
			fold_add_L[i] = F(1);
			fold_add_R[i] = F(1);
		}else if(buff_S[i] == 1){
			fold_mul[i] = F(1);
		}else{
			fold_add_L[i] = lookup_rand[0];
			fold_add_R[i] = lookup_rand[1];
			fold_lkp_O[i] = lookup_rand[0]*fold_L[i] + lookup_rand[1]*fold_R[i] - fold_O[i];
			fold_lkp[i] = F(1);
		}
	}
	F rand = F(0);
	
	F Kv = F(0);
	F Kf_O = F(0),Kf_L = F(0),Kf_R = F(0),Kf_M = F(0),Kf_lkp = F(0);
	for(int i = 0; i < BUFFER_SPACE; i++){
		Kf_O += beta[i]*fold_O[i];
		Kf_L += beta[i]*fold_L[i]*fold_add_L[i];
		Kf_R += beta[i]*fold_R[i]*fold_add_R[i];
		Kf_lkp += beta[i]*fold_lkp_O[i]*fold_lkp[i];
		Kf_M += beta[i]*fold_R[i]*fold_L[i]*(fold_mul[i]);
	}
	if( Kf_M+Kf_L+Kf_R-Kf_lkp-Kf_O != F(0) ){
		printf("Error\n");
		exit(-1);
	}
	ps += 5*sizeof(F)/1024.0;
	vector<F> R;R.push_back(F(1));
	vector<F> buff_lkp_O(BUFFER_SPACE);
	for(int i = 1; i < tr.size/BUFFER_SPACE; i++){
		read_trace(tr,buff_L,buff_R,buff_O,buff_S);
		
		F K1_O = F(0),K2_O = F(0);
		F K1_L = F(0),K2_L = F(0),K3_L = F(0);
		F K1_R = F(0),K2_R = F(0),K3_R = F(0);
		F K1_lkp = F(0),K2_lkp = F(0),K3_lkp = F(0);
		F K1_M = F(0),K2_M = F(0),K3_M = F(0),K4_M = F(0);
		compute2p_error_terms(buff_O,beta,fold_O,fold_beta,K1_O,K2_O);

		compute3p_error_terms(buff_L,buff_S,fold_L,fold_add_L ,fold_beta,beta,K1_L,K2_L,K3_L);
		for(int j = 0; j < buff_S.size(); j++){
			if(buff_S[j] == 2) buff_S[j] = 3;
		}
		compute3p_error_terms(buff_R,buff_S,fold_R,fold_add_R ,fold_beta,beta,K1_R,K2_R,K3_R);
		for(int j = 0; j < buff_lkp_O.size(); j++){
			buff_lkp_O[j] = F(0); 
			if(buff_S[j] == 0){
				buff_S[j] = -1;
			}
			if(buff_S[j] == 3){
				buff_S[j] = 4;
				buff_lkp_O[j] = lookup_rand[0]*buff_L[j] + lookup_rand[1]*buff_R[j] - buff_O[j];
			}
		}
		compute3p_error_terms(buff_lkp_O,buff_S,fold_lkp_O,fold_lkp ,fold_beta,beta,K1_lkp,K2_lkp,K3_lkp);
		
		for(int j = 0; j < buff_lkp_O.size(); j++){
			if(buff_S[j] == -1) buff_S[j] = 0;
		}

		compute4p_error_terms(buff_L,buff_R,beta,buff_S,fold_L,fold_R,fold_beta,fold_mul,K1_M,K2_M,K3_M,K4_M);
		if(K4_M + K3_L + K3_R- K3_lkp -K2_O != F(0)){
			printf("Error in gate consistency 1 : %d\n",i);
			exit(-1);
		}
		clock_t t1 = clock();
		rand = mimc_hash(K1_O,rand);
		rand = mimc_hash(K2_O,rand);
		rand = mimc_hash(K1_L,rand);
		rand = mimc_hash(K2_L,rand);
		rand = mimc_hash(K3_L,rand);
		rand = mimc_hash(K1_R,rand);
		rand = mimc_hash(K2_R,rand);
		rand = mimc_hash(K3_R,rand);
		R.push_back(rand);
		F x1 = rand,x2 = rand*x1,x3 = rand*x2,x4 = rand*x3;
		Kf_O += x1*K1_O + x2*K2_O;
		Kf_lkp += x1*K1_lkp + x2*K2_lkp + x3*K3_lkp;
		Kf_L += x1*K1_L + x2*K2_L + x3*K3_L;
		Kf_R += x1*K1_R + x2*K2_R + x3*K3_R;
		Kf_M += x1*K1_M + x2*K2_M + x3*K3_M+ x4*K4_M;
		clock_t t2 = clock();
		vt += (double)(t2-t1)/(double)(CLOCKS_PER_SEC);
		ps += 15*sizeof(F)/1024.0;
	
		for(int j = 0; j < BUFFER_SPACE; j++){
			if(buff_S[j] != 1){
				if(buff_S[j] == 0){
					fold_add_L[j] += rand;
					fold_add_R[j] += rand;
				}else{
					fold_lkp[j] += rand;
					fold_add_L[j] += rand*lookup_rand[0];
					fold_add_R[j] += rand*lookup_rand[1];
				}
			}else{
				fold_mul[j] += rand;	
			}
			fold_L[j] += rand*(buff_L[j]);
			fold_R[j] += rand*(buff_R[j]);
			fold_O[j] += rand*(buff_O[j]);
			fold_lkp_O[j] += rand*buff_lkp_O[j];
			
			fold_beta[j] += rand*beta[j];	
		}
		F s = F(0);
		for(int j = 0; j < fold_L.size(); j++){
			s += fold_beta[j]*fold_mul[j]*fold_R[j]*fold_L[j];
		}
		if(s != Kf_M){
			printf("ERRRROR %d\n",i);
			exit(-1);
		}
	}
	reset_stream(tr);
	vector<F> a = generate_randomness(5);

	F s = F(0);
	for(int i = 0; i < fold_L.size(); i++){
		s += fold_beta[i]*fold_lkp[i]*fold_lkp_O[i];
	}
	if(s != Kf_lkp){
		printf("ERRRROR\n");
	}
	vector<F> sumcheck_rand;
	F sum = a[0]*Kf_L + a[1]*Kf_R + a[2]*Kf_M + Kf_O*a[3] + Kf_lkp*a[4];  
	for(int i  = (int)log2(BUFFER_SPACE)-1; i >= 0; i--){
		vector<cubic_poly> poly1(3);
		quadruple_poly poly = quadruple_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		quadratic_poly poly2 = quadratic_poly(F_ZERO,F_ZERO,F_ZERO); 
		linear_poly l1,l2,l3,l4;
		for(int j = 0; j < 3; j++){
			poly1[j]  = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO); 
		}

		for(int j = 0; j < (1ULL<<i); j++){
			l1 = linear_poly(fold_add_L[2*j+1] - fold_add_L[2*j],fold_add_L[2*j]);
			l2 = linear_poly(fold_beta[2*j+1] - fold_beta[2*j],fold_beta[2*j]);
			l3 = linear_poly((fold_L[2*j+1] - fold_L[2*j]),fold_L[2*j]);
			poly1[0] = poly1[0] + (l1*l2*l3);
		}
		for(int j = 0; j < (1ULL<<i); j++){
			l1 = linear_poly(fold_add_R[2*j+1] - fold_add_R[2*j],fold_add_R[2*j]);
			l2 = linear_poly(fold_beta[2*j+1] - fold_beta[2*j],fold_beta[2*j]);
			l3 = linear_poly((fold_R[2*j+1] - fold_R[2*j]),fold_R[2*j]);
			poly1[1] = poly1[1]+ (l1*l2*l3);
		}
		for(int j = 0; j < (1ULL<<i); j++){
			l1 = linear_poly(fold_lkp[2*j+1] - fold_lkp[2*j],fold_lkp[2*j]);
			l2 = linear_poly(fold_beta[2*j+1] - fold_beta[2*j],fold_beta[2*j]);
			l3 = linear_poly((fold_lkp_O[2*j+1] - fold_lkp_O[2*j]),fold_lkp_O[2*j]);
			poly1[2] = poly1[2]+ (l1*l2*l3);
		}
		
		poly1[0].a = a[0]*poly1[0].a+a[1]*poly1[1].a + a[4]*poly1[2].a;
		poly1[0].b = a[0]*poly1[0].b+a[1]*poly1[1].b + a[4]*poly1[2].b;
		poly1[0].c = a[0]*poly1[0].c+a[1]*poly1[1].c + a[4]*poly1[2].c;
		poly1[0].d = a[0]*poly1[0].d+a[1]*poly1[1].d + a[4]*poly1[2].d;
		
		for(int j = 0; j < (1ULL<<i); j++){
			l1 = linear_poly(fold_mul[2*j+1] - fold_mul[2*j],fold_mul[2*j]);
			l2 = linear_poly(fold_beta[2*j+1] - fold_beta[2*j],fold_beta[2*j]);
			l3 = linear_poly(fold_L[2*j+1] - fold_L[2*j],fold_L[2*j]);
			l4 = linear_poly(fold_R[2*j+1] - fold_R[2*j],fold_R[2*j]);
			poly = poly + (l1*l2*l3*l4);
		}
		for(int j = 0; j < (1ULL<<i); j++){
			l1 = linear_poly(fold_beta[2*j+1] - fold_beta[2*j],fold_beta[2*j]);
			l2 = linear_poly(fold_O[2*j+1] - fold_O[2*j],fold_O[2*j]);
			poly2 = poly2+ l1*l2;
		}
		poly.a = a[2]*poly.a;
		poly.b = a[2]*poly.b + poly1[0].a;
		poly.c = a[2]*poly.c + poly1[0].b + a[3]*poly2.a;
		poly.d = a[2]*poly.d + poly1[0].c + a[3]*poly2.b;
		poly.e = a[2]*poly.e + poly1[0].d + a[3]*poly2.c;
		clock_t t1 = clock();
		rand = mimc_hash(poly.a,rand);
		rand = mimc_hash(poly.b,rand);
		rand = mimc_hash(poly.c,rand);
		rand = mimc_hash(poly.d,rand);
		rand = mimc_hash(poly.e,rand);
		if(sum != poly.eval(F(0)) + poly.eval(F(1))){
			printf("Error in gate consistency 2: %d\n",i);
			exit(-1);
		}
		sum = poly.eval(rand);
		sumcheck_rand.push_back(rand);
		clock_t t2 = clock();
		vt += (double)(t2-t1)/(double)(CLOCKS_PER_SEC);
		ps += 5*sizeof(F)/1024.0;
	
		for(int j = 0; j < (1ULL<<i); j++){
			fold_add_L[j] = fold_add_L[2*j] + rand*(fold_add_L[2*j+1]-fold_add_L[2*j]);
			fold_add_R[j] = fold_add_R[2*j] + rand*(fold_add_R[2*j+1]-fold_add_R[2*j]);
			fold_L[j] = fold_L[2*j] + rand*(fold_L[2*j+1]-fold_L[2*j]);
			fold_R[j] = fold_R[2*j] + rand*(fold_R[2*j+1]-fold_R[2*j]);
			fold_O[j] = fold_O[2*j] + rand*(fold_O[2*j+1]-fold_O[2*j]);
			fold_lkp[j] = fold_lkp[2*j] + rand*(fold_lkp[2*j+1]- fold_lkp[2*j]);
			fold_lkp_O[j] = fold_lkp_O[2*j] + rand*(fold_lkp_O[2*j+1]- fold_lkp_O[2*j]);
			fold_mul[j] = fold_mul[2*j] + rand*(fold_mul[2*j+1]-fold_mul[2*j]);
			fold_beta[j] = fold_beta[2*j] + rand*(fold_beta[2*j+1]-fold_beta[2*j]);
		}
	}

	clock_t t1 = clock();
	F fold_beta_eval,beta_eval = F(1);
	for(int i = 0; i < (int)log2(fold_beta.size()); i++){
		beta_eval *= (sumcheck_rand[i]*r1[i] + (F(1)-sumcheck_rand[i])*(F(1)-r1[i]));
	}
	fold_beta_eval = beta_eval;
	for(int i  = 1; i < R.size(); i++){
		fold_beta_eval += R[i]*beta_eval; 
	}
	clock_t t2 = clock();
	vt += (double)(t2-t1)/(double)(CLOCKS_PER_SEC);
		
	vector<vector<F>> Peval(8);
	for(int i = 0; i < 8; i++){
		Peval[i].resize(tr.size/BUFFER_SPACE,F(0));
	}
	vector<F> beta1;
	precompute_beta(sumcheck_rand,beta1);
	for(int i = 0; i < tr.size/BUFFER_SPACE; i++){
		read_trace(tr,buff_L,buff_R,buff_O,buff_S);
		for(int j = 0; j < BUFFER_SPACE; j++){
			Peval[0][i] += beta1[j]*buff_L[j];
			Peval[1][i] += beta1[j]*buff_R[j];
			Peval[2][i] += beta1[j]*buff_O[j];
		
			if(buff_S[j] == 0){
				Peval[3][i] += beta1[j];
				Peval[4][i] += beta1[j];
			}else if(buff_S[j] == 1){
				Peval[5][i] += beta1[j];
			}else{
				Peval[3][i] += beta1[j]*lookup_rand[0];
				Peval[4][i] += beta1[j]*lookup_rand[1];
				Peval[6][i] += beta1[j];
				Peval[7][i] += beta1[j]*(lookup_rand[0]*buff_L[j]+lookup_rand[1]*buff_R[j]-buff_O[j]);
			}
		}
	}
	
	vector<F> b = generate_randomness(8);
	vector<F> _Peval(tr.size/BUFFER_SPACE,F(0));
	vector<F> R_temp = R;
	for(int j = 0; j < Peval[0].size(); j++){
		for(int i = 0; i < Peval.size(); i++){
			_Peval[j] += b[i]*Peval[i][j];
		}
	}
	proof P = generate_2product_sumcheck_proof(R_temp,_Peval,rand, vt,ps);
	
	ps += 5*sizeof(F)/1024.0;
	t1 = clock();
	sum = fold_L[0]*b[0]+ fold_R[0]*b[1] + fold_O[0]*b[2]+
	 b[3]*fold_add_L[0] +b[4]*fold_add_R[0] + b[5]*fold_mul[0] + b[6]*fold_lkp[0] + 
	 b[7]*fold_lkp_O[0];
	if(P.q_poly[0].eval(F(0)) + P.q_poly[0].eval(F(1)) != sum){
		printf("Error in gate consistency 3\n");
		exit(-1);
	}
	t2 = clock();
	vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
}

void prove_gate_consistency(stream_descriptor tr, vector<F> r, double &vt, double &ps){
	vector<F> fold_L(BUFFER_SPACE),fold_R(BUFFER_SPACE),fold_O(BUFFER_SPACE);
	vector<F> buff_L(BUFFER_SPACE),buff_R(BUFFER_SPACE),buff_O(BUFFER_SPACE);
	vector<F> fold_add(BUFFER_SPACE);
	vector<F> fold_mul(BUFFER_SPACE);
	vector<int> buff_S(BUFFER_SPACE);

	vector<F> r1,beta,fold_beta;
	for(int i = 0; i < (int)log2(BUFFER_SPACE); i++){
		r1.push_back(r[i]);
	}
	precompute_beta(r1,beta);fold_beta = beta;
	
	read_trace(tr,buff_L,buff_R,buff_O,buff_S);
	fold_L = buff_L;
	fold_R = buff_R;
	fold_O = buff_O;
	for(int i = 0; i < BUFFER_SPACE; i++){
		fold_mul[i] = F(1) - F(buff_S[i]);
		fold_add[i] = buff_S[i];
	}
	F rand = F(0);
	
	F Kv = F(0);
	F Kf_O = F(0),Kf_L = F(0),Kf_R = F(0),Kf_M = F(0);
	for(int i = 0; i < BUFFER_SPACE; i++){
		Kf_O += beta[i]*fold_O[i];
		Kf_L += beta[i]*fold_L[i]*fold_add[i];
		Kf_R += beta[i]*fold_R[i]*fold_add[i];
		Kf_M += beta[i]*fold_R[i]*fold_L[i]*(fold_mul[i]);
	}
	ps += 4*sizeof(F)/1024.0;
	vector<F> R;R.push_back(F(1));
	for(int i = 1; i < tr.size/BUFFER_SPACE; i++){
		read_trace(tr,buff_L,buff_R,buff_O,buff_S);
		F K1_O = F(0),K2_O = F(0);
		F K1_L = F(0),K2_L = F(0),K3_L = F(0);
		F K1_R = F(0),K2_R = F(0),K3_R = F(0);
		F K1_M = F(0),K2_M = F(0),K3_M = F(0),K4_M = F(0);
		compute2p_error_terms(buff_O,beta,fold_O,fold_beta,K1_O,K2_O);
		compute3p_error_terms(buff_L,buff_S,fold_L,fold_add ,fold_beta,beta,K1_L,K2_L,K3_L);
		compute3p_error_terms(buff_R,buff_S,fold_R,fold_add ,fold_beta,beta,K1_R,K2_R,K3_R);
		compute4p_error_terms(buff_L,buff_R,beta,buff_S,fold_L,fold_R,fold_beta,fold_mul,K1_M,K2_M,K3_M,K4_M);
		if(K4_M + K3_L + K3_R-K2_O != F(0)){
			printf("Error in gate consistency 1 : %d\n",i);
			exit(-1);
		}
		clock_t t1 = clock();
		rand = mimc_hash(K1_O,rand);
		rand = mimc_hash(K2_O,rand);
		rand = mimc_hash(K1_L,rand);
		rand = mimc_hash(K2_L,rand);
		rand = mimc_hash(K3_L,rand);
		rand = mimc_hash(K1_R,rand);
		rand = mimc_hash(K2_R,rand);
		rand = mimc_hash(K3_R,rand);
		R.push_back(rand);
		F x1 = rand,x2 = rand*x1,x3 = rand*x2,x4 = rand*x3;
		Kf_O += x1*K1_O + x2*K2_O;
		Kf_L += x1*K1_L + x2*K2_L + x3*K3_L;
		Kf_R += x1*K1_R + x2*K2_R + x3*K3_R;
		Kf_M += x1*K1_M + x2*K2_M + x3*K3_M+ x4*K4_M;
		clock_t t2 = clock();
		vt += (double)(t2-t1)/(double)(CLOCKS_PER_SEC);
		ps += 12*sizeof(F)/1024.0;
	
		for(int j = 0; j < BUFFER_SPACE; j++){
			fold_add[j] += rand*F(buff_S[j]);
			fold_L[j] += rand*F(buff_L[j]);
			fold_R[j] += rand*F(buff_R[j]);
			fold_O[j] += rand*F(buff_O[j]);
			fold_mul[j] += rand*(F(1)-F(buff_S[j]));	
			fold_beta[j] += rand*beta[j];	
		}
	}
	reset_stream(tr);
	vector<F> a = generate_randomness(4);
	vector<F> sumcheck_rand;
	F sum = a[0]*Kf_L + a[1]*Kf_R + a[2]*Kf_M + Kf_O*a[3];  
	for(int i  = (int)log2(BUFFER_SPACE)-1; i >= 0; i--){
		cubic_poly poly1 = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		quadruple_poly poly = quadruple_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		quadratic_poly poly2 = quadratic_poly(F_ZERO,F_ZERO,F_ZERO); 
		linear_poly l1,l2,l3,l4;
			
		for(int j = 0; j < (1ULL<<i); j++){
			l1 = linear_poly(fold_add[2*j+1] - fold_add[2*j],fold_add[2*j]);
			l2 = linear_poly(fold_beta[2*j+1] - fold_beta[2*j],fold_beta[2*j]);
			l3 = linear_poly(a[0]*(fold_L[2*j+1] - fold_L[2*j])+a[1]*(fold_R[2*j+1] - fold_R[2*j]),
			a[0]*fold_L[2*j]+a[1]*fold_R[2*j]);
			poly1 = poly1+ (l1*l2*l3);
		}
		for(int j = 0; j < (1ULL<<i); j++){
			l1 = linear_poly(fold_mul[2*j+1] - fold_mul[2*j],fold_mul[2*j]);
			l2 = linear_poly(fold_beta[2*j+1] - fold_beta[2*j],fold_beta[2*j]);
			l3 = linear_poly(fold_L[2*j+1] - fold_L[2*j],fold_L[2*j]);
			l4 = linear_poly(fold_R[2*j+1] - fold_R[2*j],fold_R[2*j]);
			poly = poly + (l1*l2*l3*l4);
		}
		for(int j = 0; j < (1ULL<<i); j++){
			l1 = linear_poly(fold_beta[2*j+1] - fold_beta[2*j],fold_beta[2*j]);
			l2 = linear_poly(fold_O[2*j+1] - fold_O[2*j],fold_O[2*j]);
			poly2 = poly2+ l1*l2;
		}
		poly.a = a[2]*poly.a;
		poly.b = a[2]*poly.b + poly1.a;
		poly.c = a[2]*poly.c + poly1.b + a[3]*poly2.a;
		poly.d = a[2]*poly.d + poly1.c + a[3]*poly2.b;
		poly.e = a[2]*poly.e + poly1.d + a[3]*poly2.c;
		clock_t t1 = clock();
		rand = mimc_hash(poly.a,rand);
		rand = mimc_hash(poly.b,rand);
		rand = mimc_hash(poly.c,rand);
		rand = mimc_hash(poly.d,rand);
		rand = mimc_hash(poly.e,rand);
		if(sum != poly.eval(F(0)) + poly.eval(F(1))){
			printf("Error in gate consistency 2: %d\n",i);
			exit(-1);
		}
		sum = poly.eval(rand);
		sumcheck_rand.push_back(rand);
		clock_t t2 = clock();
		vt += (double)(t2-t1)/(double)(CLOCKS_PER_SEC);
		ps += 5*sizeof(F)/1024.0;
	
		for(int j = 0; j < (1ULL<<i); j++){
			fold_add[j] = fold_add[2*j] + rand*(fold_add[2*j+1]-fold_add[2*j]);
			fold_L[j] = fold_L[2*j] + rand*(fold_L[2*j+1]-fold_L[2*j]);
			fold_R[j] = fold_R[2*j] + rand*(fold_R[2*j+1]-fold_R[2*j]);
			fold_O[j] = fold_O[2*j] + rand*(fold_O[2*j+1]-fold_O[2*j]);
			fold_mul[j] = fold_mul[2*j] + rand*(fold_mul[2*j+1]-fold_mul[2*j]);
			fold_beta[j] = fold_beta[2*j] + rand*(fold_beta[2*j+1]-fold_beta[2*j]);
		}
	}

	clock_t t1 = clock();
	F fold_beta_eval,beta_eval = F(1);
	for(int i = 0; i < (int)log2(fold_beta.size()); i++){
		beta_eval *= (sumcheck_rand[i]*r1[i] + (F(1)-sumcheck_rand[i])*(F(1)-r1[i]));
	}
	fold_beta_eval = beta_eval;
	for(int i  = 1; i < R.size(); i++){
		fold_beta_eval += R[i]*beta_eval; 
	}
	clock_t t2 = clock();
	vt += (double)(t2-t1)/(double)(CLOCKS_PER_SEC);
		
	vector<vector<F>> Peval(6);
	for(int i = 0; i < 6; i++){
		Peval[i].resize(tr.size/BUFFER_SPACE,F(0));
	}
	vector<F> beta1;
	precompute_beta(sumcheck_rand,beta1);
	for(int i = 0; i < tr.size/BUFFER_SPACE; i++){
		read_trace(tr,buff_L,buff_R,buff_O,buff_S);
		for(int j = 0; j < BUFFER_SPACE; j++){
			Peval[0][i] += beta1[j]*buff_L[j];
			Peval[1][i] += beta1[j]*buff_R[j];
			Peval[2][i] += beta1[j]*buff_O[j];
			Peval[3][i] += beta1[j]*F(buff_S[j]);
			Peval[4][i] += beta1[j]*(F(1)-F(buff_S[j]));
			Peval[5][i] += beta1[j]*beta[j];
		}
	}
	
	vector<F> b = generate_randomness(6);
	vector<F> _Peval(tr.size/BUFFER_SPACE,F(0));
	vector<F> R_temp = R;
	for(int j = 0; j < Peval[0].size(); j++){
		for(int i = 0; i < Peval.size(); i++){
			_Peval[j] += b[i]*Peval[i][j];
		}
	}
	proof P = generate_2product_sumcheck_proof(R_temp,_Peval,rand, vt,ps);
	
	ps += 5*sizeof(F)/1024.0;
	t1 = clock();
	sum = fold_L[0]*b[0]+ fold_R[0]*b[1] + fold_O[0]*b[2]+
	 b[3]*fold_add[0] + b[4]*fold_mul[0] + b[5]*fold_beta[0];
	if(P.q_poly[0].eval(F(0)) + P.q_poly[0].eval(F(1)) != sum){
		printf("Error in gate consistency 3\n");
		exit(-1);
	}
	t2 = clock();
	vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
}

void commit_layers(stream_descriptor fd, vector<stream_descriptor> &fd_com, vector<vector<vector<_hash>>> &MT_hashes, int batches , int layer_id, int distance){
	printf("%lld,%d\n",fd.size,1ULL<<layer_id);
	int size = fd.size/(1ULL<<layer_id);
	if(batches-1 <= 0 ) return;
	
	fd_com.resize(batches-1);
	MT_hashes.resize(batches-1);
	for(int i = 0; i < batches-1; i++){
		fd_com[i].name = "PC_layer";fd_com[i].size = size/(1ULL<<(distance*i));
		fd_com[i].layer = layer_id + i*distance;
		reset_stream(fd_com[i]);
		_hash comm;
		init_commitment(false);
		printf("Committing to: %d\n",fd_com[i].size);
		if(fd_com[i].size > BUFFER_SPACE){
			commit(fd_com[i] ,comm, MT_hashes[i]);
		}
		//printf("OK\n");
	}
}


void open_layers(vector<stream_descriptor> &fd_com, vector<vector<vector<_hash>>> &MT_hashes, double &vt, double &ps){
	for(int i = 0; i < fd_com.size(); i++){
		if(fd_com[i].size > BUFFER_SPACE){
			open(fd_com[i],generate_randomness((int)log2(fd_com[i].size)),MT_hashes[i],vt,ps);
		}
	}
}


void generate_claims_opt(stream_descriptor fd, vector<F> r, vector<F> &claims, int batches , int layer_id, int distance){
	vector<vector<F>> beta(batches);
	int size = fd.size/(1ULL<<layer_id);
	
	vector<vector<F>> remaining_betas(batches);
	vector<vector<F>> initial_r(batches);
	vector<vector<F>> remaining_r(batches);
	for(int i = 0; i < batches; i++){
		for(int j = 0; j < ((int)log2(BUFFER_SPACE) - i*distance); j++){
			initial_r[i].push_back(r[j]);
		}
		precompute_beta(initial_r[i],beta[i]);
		for(int j = ((int)log2(BUFFER_SPACE) - i*distance); j < ((int)log2(size/2) - i*distance); j++){
			remaining_r[i].push_back(r[j]);
		}
		precompute_beta(remaining_r[i],remaining_betas[i]);
	}
	vector<vector<F>> V(batches);
	for(int i = 0; i < batches; i++){
		V[i].resize(4*BUFFER_SPACE/(1ULL<<(i*distance)));
	}
	claims.resize(batches);
	for(int i = 0; i < claims.size(); i++)claims[i] = F(0);

	for(int i = 0; i < size/(4*BUFFER_SPACE); i++){
		read_mul_tree_data(fd, V, 4*BUFFER_SPACE, layer_id, distance);

		for(int j = 0; j < batches; j++){
			for(int k = 0; k < V[j].size()/4; k++){
				claims[j] += remaining_betas[j][i]*beta[j][k]*V[j][2*k]*V[j][2*k+1];
			}		
		}
		for(int j = 0; j < batches; j++){
			for(int k = 0; k < V[j].size()/4; k++){
				claims[j] += remaining_betas[j][i+remaining_betas[j].size()/2]*beta[j][k]*V[j][2*k+V[j].size()/2]*V[j][2*k+1+V[j].size()/2];
			}		
		}

	}
	
}


void generate_claims(stream_descriptor fd, vector<F> r, vector<F> &claims, int batches , int layer_id, int distance){
	vector<vector<F>> beta(batches);
	int size = fd.size/(1ULL<<layer_id);
	
	vector<vector<F>> remaining_betas(batches);
	vector<vector<F>> initial_r(batches);
	vector<vector<F>> remaining_r(batches);
	for(int i = 0; i < batches; i++){
		for(int j = 0; j < ((int)log2(BUFFER_SPACE) - i*distance); j++){
			initial_r[i].push_back(r[j]);
		}
		precompute_beta(initial_r[i],beta[i]);
		for(int j = ((int)log2(BUFFER_SPACE) - i*distance); j < ((int)log2(size/2) - i*distance); j++){
			remaining_r[i].push_back(r[j]);
		}
		precompute_beta(remaining_r[i],remaining_betas[i]);
	}
	vector<vector<F>> V(batches);
	for(int i = 0; i < batches; i++){
		V[i].resize(2*BUFFER_SPACE/(1ULL<<(i*distance)));
	}
	claims.resize(batches);
	for(int i = 0; i < claims.size(); i++)claims[i] = F(0);

	for(int i = 0; i < size/(2*BUFFER_SPACE); i++){
		read_mul_tree_data(fd, V, 2*BUFFER_SPACE, layer_id, distance);

		for(int j = 0; j < batches; j++){
			for(int k = 0; k < V[j].size()/2; k++){
				claims[j] += remaining_betas[j][i]*beta[j][k]*V[j][2*k]*V[j][2*k+1];
			}		
		}
	}
	
}

void batch_prod(vector<vector<F>> &fold_buff1,vector<vector<F>> &fold_buff2,vector<vector<F>> &fold_buff3, vector<vector<F>> &buff1, vector<vector<F>> &buff2,
	vector<vector<F>> &buff3, int batches, vector<F> &R, F &Kf, vector<F> &K_partial, vector<vector<F>> &remaining_betas, vector<F> a, 
	int i,double &vt, double &ps){
	
	vector<F> K3(batches,F(0));
	F K1 = F(0),K2 = F(0);
	F rand = R[R.size()-1];
	for(int j = 0; j < batches; j++){
		F K1_temp = F(0),K2_temp = F(0);
		// Compute error terms
		for(int k = 0; k < buff1[j].size(); k++){
			F t1 = buff1[j][k]*fold_buff2[j][k] + buff2[j][k]*fold_buff1[j][k];
			F t2 = buff1[j][k]*buff2[j][k];
			K1_temp += fold_buff3[j][k]*t1 + buff3[j][k]*fold_buff1[j][k]*fold_buff2[j][k];
			K2_temp += buff3[j][k]*t1 + fold_buff3[j][k]*t2;
			K3[j] += t2*buff3[j][k];
		}
		K1 += a[j]*K1_temp;
		K2 += a[j]*K2_temp;
	}
	clock_t t1 = clock();
	rand = mimc_hash(K1,rand);
	rand = mimc_hash(K2,rand);
	for(int j = 0; j < batches; j++){
		rand = mimc_hash(K3[j],rand);
	}
	F x1 = rand, x2 = rand*x1, x3 = rand*x2;
	for(int j = 0; j < batches; j++){
		K_partial[j] += remaining_betas[j][i]*K3[j];
		Kf += x3*a[j]*K3[j];
	}
	Kf += x2*K2 + x1*K1;
	R.push_back(rand);
	clock_t t2 = clock();
	vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	ps += (1 + K3.size())*sizeof(F)/1024.0;
	for(int j = 0; j < batches; j++){
		for(int k = 0; k < buff1[j].size(); k++){
			fold_buff1[j][k] += rand*buff1[j][k];
			fold_buff2[j][k] += rand*buff2[j][k];
			fold_buff3[j][k] += rand*buff3[j][k];
		}
	}
}

void permute_partial_evals(vector<F> &R, vector<vector<F>> &partial_evals){
	vector<F> temp_R(R.size());
	int counter =0;
	for(int i = 0; i < R.size()/2; i++){
		temp_R[counter++] = R[2*i];
	}
	for(int i = 0; i < R.size()/2; i++){
		temp_R[counter++] = R[2*i+1];
	}
	R = temp_R; 
}

void generate_3product_sumcheck_beta_stream_batch_optimized(stream_descriptor fd, vector<vector<F>> r, int batches, int distance, int layer_id,
		vector<F> old_claims, vector<F> &new_claims, vector<vector<F>> &new_r, double &vt, double &ps){
	
	vector<vector<F>> fold_buff1(batches),fold_buff2(batches),fold_buff3(batches);
	vector<vector<F>> buff1(batches),buff2(batches),buff3(batches);
	size_t size = fd.size/(1ULL<<layer_id);
	vector<int> sizes(batches);
	for(int i = 0; i < batches; i++){
		sizes[i] = BUFFER_SPACE/(1ULL<<(i*distance));
		fold_buff1[i].resize(BUFFER_SPACE/(1ULL<<(i*distance)));
		fold_buff2[i].resize(BUFFER_SPACE/(1ULL<<(i*distance)));
		buff1[i].resize(BUFFER_SPACE/(1ULL<<(i*distance)));
		buff2[i].resize(BUFFER_SPACE/(1ULL<<(i*distance)));
	}
	vector<vector<F>> remaining_betas(batches);
	vector<vector<F>> initial_r(batches);
	vector<vector<F>> remaining_r(batches);
	
	for(int i = 0; i < batches; i++){
		for(int j = 0; j < ((int)log2(BUFFER_SPACE) - i*distance); j++){
			initial_r[i].push_back(r[i][j]);
		}
		precompute_beta(initial_r[i],buff3[i]);
		fold_buff3[i] = buff3[i];
		for(int j = ((int)log2(BUFFER_SPACE) - i*distance); j < ((int)log2(size/2) - i*distance); j++){
			remaining_r[i].push_back(r[i][j]);
		}
		precompute_beta(remaining_r[i],remaining_betas[i]);
	}
	
	
	vector<vector<F>> V(batches);
	for(int i = 0; i < batches; i++){
		V[i].resize(4*BUFFER_SPACE/(1ULL<<(i*distance)));
	}
	clock_t rt1 = clock();
	read_mul_tree_data(fd, V, 4*BUFFER_SPACE, layer_id, distance);
	clock_t rt2 = clock();
	routine_time += (double)(rt2-rt1)/(double)CLOCKS_PER_SEC;
	
	vector<F> K_partial(batches,F(0));
	clock_t _t1,_t2;
	_t1 = clock();
	
	for(int i = 0; i < V.size(); i++){
		for(int j = 0; j < fold_buff1[i].size(); j++){
			fold_buff1[i][j] = V[i][2*j];
			fold_buff2[i][j] = V[i][2*j+1];
		}
		for(int j = 0; j < fold_buff1[i].size(); j++){
			K_partial[i] += fold_buff1[i][j]*fold_buff2[i][j]*fold_buff3[i][j];
		}
	}
	
	vector<F> a = generate_randomness(batches);
	F Kf = F(0), rand = F(0);
	vector<F> R;R.push_back(F(1));
	for(int i = 0; i < a.size(); i++){
		Kf += a[i]*K_partial[i];
		K_partial[i] *= remaining_betas[i][0];
	}
	
	ps += (1+K_partial.size())*sizeof(F)/1024.0;
	
	for(int j = 0; j  < batches; j++){
		for(int k = 0; k < buff1[j].size(); k++){
			buff1[j][k] = V[j][2*k+2*buff1[j].size()];
			buff2[j][k] = V[j][2*k+1+2*buff1[j].size()];
		}
	}
	batch_prod(fold_buff1,fold_buff2,fold_buff3, buff1, buff2, buff3, batches, R, Kf, K_partial,remaining_betas,a,remaining_betas[0].size()/2, vt, ps);
	for(int i = 1; i < size/(4*BUFFER_SPACE); i++){
		rt1 = clock();
		read_mul_tree_data(fd, V, 4*BUFFER_SPACE, layer_id, distance);
		rt2 = clock();
		routine_time += (double)(rt2-rt1)/(double)CLOCKS_PER_SEC;
		for(int j = 0; j  < batches; j++){
			for(int k = 0; k < buff1[j].size(); k++){
				buff1[j][k] = V[j][2*k];
				buff2[j][k] = V[j][2*k+1];
			}
		}
		batch_prod(fold_buff1,fold_buff2,fold_buff3, buff1, buff2, buff3, batches, R, Kf,K_partial,remaining_betas,a,i, vt, ps);
		for(int j = 0; j  < batches; j++){
			for(int k = 0; k < buff1[j].size(); k++){
				buff1[j][k] = V[j][2*k+2*buff1[j].size()];
				buff2[j][k] = V[j][2*k+1+2*buff1[j].size()];
			}
		}
		batch_prod(fold_buff1,fold_buff2,fold_buff3, buff1, buff2, buff3, batches, R, Kf,K_partial,remaining_betas,a,i+remaining_betas[0].size()/2, vt, ps);
		
	}
	_t2 = clock();
	//printf("~ %d, %lf\n",size/(4*BUFFER_SPACE),(double)(_t2-_t1)/CLOCKS_PER_SEC);
	reset_stream(fd);
	
	for(int i = 0; i < old_claims.size(); i++){
		if(K_partial[i] != old_claims[i]){
			printf("Error in sumcheck 0 %d\n",i);
			//exit(-1);
		}
	}
	_t1 = clock();
	
	for(int i = 0; i < fold_buff1.size(); i++){
		buff1[i].clear();
		buff2[i].clear();
		vector<F>(buff1[i]).swap(buff1[i]);
		vector<F>(buff2[i]).swap(buff2[i]);
	}
	buff1.clear();buff2.clear();
	vector<vector<F>>(buff1).swap(buff1);
	vector<vector<F>>(buff2).swap(buff2);
	
	proof P1 = batch_3product_sumcheck(fold_buff1, fold_buff2, fold_buff3, a,vt,ps);
	
	for(int i = 0; i < fold_buff1.size(); i++){
		fold_buff1[i].clear();
		fold_buff2[i].clear();
		fold_buff3[i].clear();
		vector<F>(fold_buff1[i]).swap(fold_buff1[i]);
		vector<F>(fold_buff2[i]).swap(fold_buff2[i]);
		vector<F>(fold_buff3[i]).swap(fold_buff3[i]);
	}	
	fold_buff1.clear();fold_buff2.clear();fold_buff3.clear();
	vector<vector<F>>(fold_buff1).swap(fold_buff1);
	vector<vector<F>>(fold_buff2).swap(fold_buff2);
	vector<vector<F>>(fold_buff3).swap(fold_buff3);
	
	
	clock_t t1 = clock();
	if(P1.c_poly[0].eval(F(0)) + P1.c_poly[0].eval(F(1)) != Kf){
		printf("Error in sumcheck 1\n");
		exit(-1);
	}
	
	for(int i = 0; i < batches; i++){
		F fold_beta_eval,beta_eval = F(1);
		for(int j = 0; j < initial_r[i].size(); j++){
			beta_eval *= (P1.randomness[0][j]*initial_r[i][j] + (F(1)-P1.randomness[0][j])*(F(1)-initial_r[i][j]));
		}
		fold_beta_eval = beta_eval;
		for(int i  = 1; i < R.size(); i++){
			fold_beta_eval += R[i]*beta_eval; 
		}
	}
	clock_t t2 = clock();
	
	vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	if(R.size() == 1){
		//printf("!OK\n");
	
		F pad_randomness = random();
		new_r.resize(batches);
		for(int i = 0; i < batches; i++){
			new_r[i].clear();
			new_r[i] = P1.randomness[0];
			new_r[i].insert(new_r[i].begin(),pad_randomness);
		}
		for(int i = 0; i < new_claims.size(); i++){
			new_claims[i] = (F(1) - pad_randomness)*P1.vr[0] +pad_randomness*P1.vr[1];
		}
		return;
	}
	
	vector<vector<F>> Partial_Evals(2*batches);
	vector<vector<F>> beta(batches);
	for(int i = 0; i < batches; i++){
		Partial_Evals[2*i].resize(R.size(),F(0));
		Partial_Evals[2*i+1].resize(R.size(),F(0));
		vector<F> r;
		for(int j = 0; j < (int)log2(sizes[i]); j++){
			r.push_back(P1.randomness[0][j]);
		}
		precompute_beta(r,beta[i]);
	}
	
	for(int i = 0; i < size/(4*BUFFER_SPACE); i++){
		rt1 = clock();
		read_mul_tree_data(fd, V, 4*BUFFER_SPACE, layer_id, distance);
		rt2 = clock();
		routine_time += (double)(rt2-rt1)/(double)CLOCKS_PER_SEC;
		for(int k = 0; k < batches; k++){
			for(int j = 0; j < V[k].size()/4; j++){
				Partial_Evals[2*k][i] += beta[k][j]*V[k][2*j];
				Partial_Evals[2*k][i+R.size()/2] += beta[k][j]*V[k][2*j + V[k].size()/2];
				Partial_Evals[2*k+1][i] += beta[k][j]*V[k][2*j+1];
				Partial_Evals[2*k+1][i+R.size()/2] += beta[k][j]*V[k][2*j+1 + V[k].size()/2];
			}
		}
	}
	
	permute_partial_evals(R, Partial_Evals);
	vector<F> b = generate_randomness(2*batches);
	vector<F> aggr_eval(R.size(),F(0));
	for(int i = 0; i < Partial_Evals.size(); i++){
		for(int j = 0; j < aggr_eval.size(); j++){
			aggr_eval[j] += b[i]*Partial_Evals[i][j];
		}
	}
	
	vector<F> temp_R = R;
	proof P2 = generate_2product_sumcheck_proof(temp_R,aggr_eval,rand,vt,ps);
	temp_R.clear();
	vector<F>(temp_R).swap(temp_R);
	
	t1 = clock();
	F sum = F(0);
	for(int i = 0; i < b.size()/2; i++){
		sum += b[2*i]*P1.vr[3*i];
		sum += b[2*i+1]*P1.vr[3*i+1];
	}
	
	if(sum !=( P2.q_poly[0].eval(F(0)) + P2.q_poly[0].eval(F(1)))){
		printf("Error in sumcheck 2\n");
		exit(-1);
	}
	t2 = clock();
	vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	new_r.resize(batches);
	F pad_randomness = random();
	for(int i = 0; i < new_r.size(); i++){
		new_r[i].clear();
		new_r[i].push_back(pad_randomness);
		for(int j = 0; j < (int)log2(BUFFER_SPACE) - i*distance; j++){
			new_r[i].push_back(P1.randomness[0][j]);
		}
		for(int j = 0; j < P2.randomness[0].size(); j++){
			new_r[i].push_back(P2.randomness[0][j]);
		}
	}
	//new_r = P1.randomness[0];
	//new_r.insert(new_r.end(),P2.randomness[0].begin(),P2.randomness[0].end());
	//new_r.insert(new_r.begin(),random());
	new_claims.resize(batches);
	for(int i = 0; i < new_claims.size(); i++){
		new_claims[i] = (F(1) - pad_randomness)*evaluate_vector(Partial_Evals[2*i],P2.randomness[0]) +
		pad_randomness*evaluate_vector(Partial_Evals[2*i+1],P2.randomness[0]);
	}
	_t2 = clock();
	//printf("~ %d, %lf\n",size/(4*BUFFER_SPACE),(double)(_t2-_t1)/CLOCKS_PER_SEC);
	
}

void generate_3product_sumcheck_beta_stream_batch(stream_descriptor fd, vector<vector<F>> r, int batches, int distance, int layer_id,
		vector<F> old_claims, vector<F> &new_claims, vector<vector<F>> &new_r, double &vt, double &ps){
	
	vector<vector<F>> fold_buff1(batches),fold_buff2(batches),fold_buff3(batches);
	vector<vector<F>> buff1(batches),buff2(batches),buff3(batches);
	int size = fd.size/(1ULL<<layer_id);
	vector<int> sizes(batches);
	for(int i = 0; i < batches; i++){
		sizes[i] = BUFFER_SPACE/(1ULL<<(i*distance));
		fold_buff1[i].resize(BUFFER_SPACE/(1ULL<<(i*distance)));
		fold_buff2[i].resize(BUFFER_SPACE/(1ULL<<(i*distance)));
		buff1[i].resize(BUFFER_SPACE/(1ULL<<(i*distance)));
		buff2[i].resize(BUFFER_SPACE/(1ULL<<(i*distance)));
	}
	vector<vector<F>> remaining_betas(batches);
	vector<vector<F>> initial_r(batches);
	vector<vector<F>> remaining_r(batches);
	
	
	for(int i = 0; i < batches; i++){
		for(int j = 0; j < ((int)log2(BUFFER_SPACE) - i*distance); j++){
			initial_r[i].push_back(r[i][j]);
		}
		precompute_beta(initial_r[i],buff3[i]);
		fold_buff3[i] = buff3[i];
		for(int j = ((int)log2(BUFFER_SPACE) - i*distance); j < ((int)log2(size/2) - i*distance); j++){
			remaining_r[i].push_back(r[i][j]);
		}
		precompute_beta(remaining_r[i],remaining_betas[i]);
	}
	
	
	vector<vector<F>> V(batches);
	for(int i = 0; i < batches; i++){
		V[i].resize(2*BUFFER_SPACE/(1ULL<<(i*distance)));
	}
	clock_t rt1 = clock();
	read_mul_tree_data(fd, V, 2*BUFFER_SPACE, layer_id, distance);
	clock_t rt2 = clock();
	routine_time += (double)(rt2-rt1)/(double)CLOCKS_PER_SEC;
	
	vector<F> K_partial(batches,F(0));
	
	for(int i = 0; i < V.size(); i++){
		for(int j = 0; j < fold_buff1[i].size(); j++){
			fold_buff1[i][j] = V[i][2*j];
			fold_buff2[i][j] = V[i][2*j+1];
		}
		for(int j = 0; j < fold_buff1[i].size(); j++){
			K_partial[i] += fold_buff1[i][j]*fold_buff2[i][j]*fold_buff3[i][j];
		}
	}
	
	vector<F> a = generate_randomness(batches);
	F Kf = F(0), rand = F(0);
	vector<F> R;R.push_back(F(1));
	for(int i = 0; i < a.size(); i++){
		Kf += a[i]*K_partial[i];
		K_partial[i] *= remaining_betas[i][0];
	}
	
	ps += (1+K_partial.size())*sizeof(F)/1024.0;

	for(int i = 1; i < size/(2*BUFFER_SPACE); i++){
		rt1 = clock();
		read_mul_tree_data(fd, V, 2*BUFFER_SPACE, layer_id, distance);
		rt2 = clock();
		routine_time += (double)(rt2-rt1)/(double)CLOCKS_PER_SEC;

		vector<F> K3(batches,F(0));
		F K1 = F(0),K2 = F(0);
		for(int j = 0; j < batches; j++){
			for(int k = 0; k < buff1[j].size(); k++){
				buff1[j][k] = V[j][2*k];
				buff2[j][k] = V[j][2*k+1];
			}
			F K1_temp = F(0),K2_temp = F(0);
			// Compute error terms
			for(int k = 0; k < buff1[j].size(); k++){
				F t1 = buff1[j][k]*fold_buff2[j][k] + buff2[j][k]*fold_buff1[j][k];
				F t2 = buff1[j][k]*buff2[j][k];
				K1_temp += fold_buff3[j][k]*t1 + buff3[j][k]*fold_buff1[j][k]*fold_buff2[j][k];
				K2_temp += buff3[j][k]*t1 + fold_buff3[j][k]*t2;
				K3[j] += t2*buff3[j][k];
			}
			K1 += a[j]*K1_temp;
			K2 += a[j]*K2_temp;
		}
		clock_t t1 = clock();
		rand = mimc_hash(K1,rand);
		rand = mimc_hash(K2,rand);
		for(int j = 0; j < batches; j++){
			rand = mimc_hash(K3[j],rand);
		}
		F x1 = rand, x2 = rand*x1, x3 = rand*x2;
		for(int j = 0; j < batches; j++){
			K_partial[j] += remaining_betas[j][i]*K3[j];
			Kf += x3*a[j]*K3[j];
		}
		Kf += x2*K2 + x1*K1;
		R.push_back(rand);
		clock_t t2 = clock();
		vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
		ps += (1 + K3.size())*sizeof(F)/1024.0;
		for(int j = 0; j < batches; j++){
			for(int k = 0; k < buff1[j].size(); k++){
				fold_buff1[j][k] += rand*buff1[j][k];
				fold_buff2[j][k] += rand*buff2[j][k];
				fold_buff3[j][k] += rand*buff3[j][k];
			}
		}
	}

	reset_stream(fd);
	
	
	for(int i = 0; i < old_claims.size(); i++){
		if(K_partial[i] != old_claims[i]){
			printf("Error in sumcheck 0 %d\n",i);
			//exit(-1);
		}
	}
	
	proof P1 = batch_3product_sumcheck(fold_buff1, fold_buff2, fold_buff3, a,vt,ps);
	

	
	clock_t t1 = clock();
	if(P1.c_poly[0].eval(F(0)) + P1.c_poly[0].eval(F(1)) != Kf){
		printf("Error in sumcheck 1\n");
		exit(-1);
	}
	for(int i = 0; i < batches; i++){
		F fold_beta_eval,beta_eval = F(1);
		for(int j = 0; j < initial_r[i].size(); j++){
			beta_eval *= (P1.randomness[0][j]*initial_r[i][j] + (F(1)-P1.randomness[0][j])*(F(1)-initial_r[i][j]));
		}
		fold_beta_eval = beta_eval;
		for(int i  = 1; i < R.size(); i++){
			fold_beta_eval += R[i]*beta_eval; 
		}
	}
	clock_t t2 = clock();
	vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	
	if(R.size() == 1){
		F pad_randomness = random();
		new_r.resize(batches);
		for(int i = 0; i < batches; i++){
			new_r[i].clear();
			new_r[i] = P1.randomness[0];
			new_r[i].insert(new_r[i].begin(),pad_randomness);
		}
		for(int i = 0; i < new_claims.size(); i++){
			new_claims[i] = (F(1) - pad_randomness)*P1.vr[0] +pad_randomness*P1.vr[1];
		}
		return;
	}
	vector<vector<F>> Partial_Evals(2*batches);
	vector<vector<F>> beta(batches);
	for(int i = 0; i < batches; i++){
		Partial_Evals[2*i].resize(R.size(),F(0));
		Partial_Evals[2*i+1].resize(R.size(),F(0));
		vector<F> r;
		for(int j = 0; j < (int)log2(sizes[i]); j++){
			r.push_back(P1.randomness[0][j]);
		}
		precompute_beta(r,beta[i]);
	}
	
	for(int i = 0; i < size/(2*BUFFER_SPACE); i++){
		rt1 = clock();
		read_mul_tree_data(fd, V, 2*BUFFER_SPACE, layer_id, distance);
		rt2 = clock();
		routine_time += (double)(rt2-rt1)/(double)CLOCKS_PER_SEC;
		for(int k = 0; k < batches; k++){
			
			for(int j = 0; j < V[k].size()/2; j++){
				Partial_Evals[2*k][i] += beta[k][j]*V[k][2*j];
				Partial_Evals[2*k+1][i] += beta[k][j]*V[k][2*j+1];
			}
		}
	}

	vector<F> b = generate_randomness(2*batches);
	vector<F> aggr_eval(R.size(),F(0));
	for(int i = 0; i < Partial_Evals.size(); i++){
		for(int j = 0; j < aggr_eval.size(); j++){
			aggr_eval[j] += b[i]*Partial_Evals[i][j];
		}
	}
	vector<F> temp_R = R;
	
	proof P2 = generate_2product_sumcheck_proof(temp_R,aggr_eval,rand,vt,ps);
	t1 = clock();
	F sum = F(0);
	for(int i = 0; i < b.size()/2; i++){
		sum += b[2*i]*P1.vr[3*i];
		sum += b[2*i+1]*P1.vr[3*i+1];
	}
	if(sum !=( P2.q_poly[0].eval(F(0)) + P2.q_poly[0].eval(F(1)))){
		printf("Error in sumcheck 2\n");
		exit(-1);
	}
	t2 = clock();
	vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	/// NEEED TO CHANGE THIS
	new_r.resize(batches);
	F pad_randomness = random();
	for(int i = 0; i < new_r.size(); i++){
		new_r[i].clear();
		new_r[i].push_back(pad_randomness);
		for(int j = 0; j < (int)log2(BUFFER_SPACE) - i*distance; j++){
			new_r[i].push_back(P1.randomness[0][j]);
		}
		for(int j = 0; j < P2.randomness[0].size(); j++){
			new_r[i].push_back(P2.randomness[0][j]);
		}
	}
	//new_r = P1.randomness[0];
	//new_r.insert(new_r.end(),P2.randomness[0].begin(),P2.randomness[0].end());
	//new_r.insert(new_r.begin(),random());
	new_claims.resize(batches);
	for(int i = 0; i < new_claims.size(); i++){
		new_claims[i] = (F(1) - pad_randomness)*evaluate_vector(Partial_Evals[2*i],P2.randomness[0]) +
		pad_randomness*evaluate_vector(Partial_Evals[2*i+1],P2.randomness[0]);
	}
}

void generate_3product_sumcheck_beta_stream(stream_descriptor fd1, stream_descriptor fd2, vector<F> r, double &vt, double &ps){
	vector<F> fold_buff1(BUFFER_SPACE),fold_buff2(BUFFER_SPACE),fold_buff3(BUFFER_SPACE);
	vector<F> buff1(BUFFER_SPACE),buff2(BUFFER_SPACE);
	vector<F> beta1,beta2;
	vector<F> r1,r2;
	for(int i = 0; i < (int)log2(BUFFER_SPACE); i++){
		r1.push_back(r[i]);
	}
	F Kv = F(0),Kf = F(0);
	F rand = F(0);
	vector<F> R;
	F rand_sum = 1;
	precompute_beta(r1,beta1);
	read_stream(fd1,fold_buff1,BUFFER_SPACE);
	read_stream(fd2,fold_buff2,BUFFER_SPACE);
	fold_buff3 = beta1;
	for(int i = 0; i <fold_buff1.size(); i++){
		Kf += fold_buff1[i]*fold_buff2[i]*beta1[i];
	}
	Kv += Kf;
	R.push_back(F(1));
	for(int i = 1; i < fd1.size/BUFFER_SPACE; i++){
		read_stream(fd1,buff1,BUFFER_SPACE);
		read_stream(fd2,buff2,BUFFER_SPACE);
		F K = F(0),K1 = F(0),K2 = F(0);
		for(int j = 0; j < buff1.size(); j++){
			F t1 = buff1[j]*fold_buff2[j] + buff2[j]*fold_buff1[j];
			F t2 = buff1[j]*buff2[j];
			K1 += fold_buff3[j]*t1 + beta1[j]*fold_buff1[j]*fold_buff2[j];
			K2 += beta1[j]*t1 + fold_buff3[j]*t2;
			K += t2*beta1[j];
		}
		
		rand = mimc_hash(K1,rand);
		rand = mimc_hash(K2,rand);
		rand = mimc_hash(K,rand);
		
		Kf += rand*K1 + rand*rand*K2 + rand*rand*rand*K;
		Kv += K;

		R.push_back(rand);
		rand_sum += 1;
		for(int j = 0; j < buff1.size(); j++){
			fold_buff1[j] += rand*buff1[j];
			fold_buff2[j] += rand*buff2[j];
			fold_buff3[j] += rand*beta1[j];
		}
	}

	proof P1 = _generate_3product_sumcheck_proof(fold_buff1,fold_buff2,fold_buff3,rand,vt,ps);
	if(P1.c_poly[0].eval(F(0)) + P1.c_poly[0].eval(F(1)) != Kf){
		printf("Error 1\n");
		exit(-1);
	}
	precompute_beta(P1.randomness[0],beta2);
	vector<F> Peval1(fd1.size/BUFFER_SPACE,F(0)),Peval2(fd1.size/BUFFER_SPACE,F(0));
	for(int i = 0; i < fd1.size/BUFFER_SPACE; i++){
		read_stream(fd1,buff1,BUFFER_SPACE);
		read_stream(fd2,buff2,BUFFER_SPACE);
		for(int j = 0; j < buff1.size(); j++){
			Peval1[i] += buff1[j]*beta2[j];
			Peval2[i] += buff2[j]*beta2[j];			
		}
	}
	F b = random();
	vector<F> aggr_eval(Peval1.size());
	for(int i = 0; i < Peval1.size(); i++){
		aggr_eval[i] = Peval1[i] + b*Peval2[i];
	}
	vector<F> temp_R = R;
	proof P2 = generate_2product_sumcheck_proof(temp_R,aggr_eval,b,vt,ps);
	if(P2.q_poly[0].eval(F(0)) + P2.q_poly[0].eval(F(1)) != P1.vr[0] +b*P1.vr[1]){
		printf("Error 2\n");
	}
	if(P2.vr[0] != evaluate_vector(temp_R,P2.randomness[0])){
		printf("Error 3\n");
	}
}

struct proof generate_3product_sumcheck_proof_naive(vector<F> &v1, vector<F> &v2, vector<F> &v3, vector<F> r){
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())),F(0));
	vector<cubic_poly> p;
	for(int i = 0; i < r.size(); i++){
		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		linear_poly l1,l2,l3;
		
		int L = 1 << (r.size() -1- i);
		for(int j = 0; j < L; j++){
			if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
				l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
				//q1 = quadratic_poly()
				l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
				l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
				temp_poly = l1*l2*l3;
				poly = poly + temp_poly;

			}
			v1[j] = (F(1)-r[i])*v1[2*j] + r[i]*v1[2*j+1];
			if(v2[2*j] == F(0) && v2[2*j+1] == F(0)){
				v2[j] = F(0);
				v3[j] = F(1);
			}else{

				v2[j] = v2[2*j] + r[i]*(v2[2*j+1]-v2[2*j]);
				v3[j] = v3[2*j] + r[i]*(v3[2*j+1]-v3[2*j]);	

			}
		}
		p.push_back(poly);
	}
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v1[0]);

	return Pr;
}


// takes as input vectors x of equal size and for each 
// vector outputs Prod_i = x[0]*x[1]*x[2]...x[N]
vector<F> prove_multiplication_tree_stream_shallow(stream_descriptor fd,int vectors,int size, F previous_r, int distance, vector<F> prev_x, bool naive,
  double &vt, double &ps){
	
	// Initialize total input
	
	int depth = (int)log2(size);
    
	
	    
    if(size*vectors <= 2*BUFFER_SPACE){
		vector<F> v(size*vectors);
        vector<vector<F>> input(vectors);
        for(int i = 0; i < vectors; i++){
            input[i].resize(size);
        }
        
		
		read_stream(fd,v,size*vectors);	    
        
        int counter = 0;
        for(int i = 0; i < vectors; i++){
            for(int j = 0; j < size; j++){
                input[i][j] = v[counter];
                counter++;
            }
        }
		mul_tree_proof P1 = prove_multiplication_tree_new(input,previous_r,prev_x,vt,ps);
		return P1.output;
	}
	int layers;
	if(fd.name == "wiring_consistency_check"){
		layers = (int)log2(size*vectors/(BUFFER_SPACE));
		if(layers%distance != 0 && layers > distance){
			layers = distance+layers - (layers%distance);
			//layers = layers - (layers%distance);
		}
	}else{
		layers = (int)log2(((size_t)size*vectors)/(2*BUFFER_SPACE));
		//printf(">> %d\n",layers);
		if(layers%distance != 0 && layers > distance){
			layers =distance+ layers - (layers%distance);
			//layers = layers - (layers%distance);
		}
	}
	vector<stream_descriptor> fd_com;
	vector<vector<vector<_hash>>> MT_hashes;
	if(!naive){
		int batches = layers/distance;
		commit_layers(fd, fd_com ,MT_hashes, batches, distance-1, distance);
	}
	
	
	
	vector<F> buff1(fd.size/(1ULL<<layers));
	
	
	if(buff1.size() <= BUFFER_SPACE){
		BUFFER_SPACE_tr = buff1.size()/8;
	}
	read_mul_tree_layer(fd, buff1, buff1.size(), layers);
	
	
	BUFFER_SPACE_tr = BUFFER_SPACE/8;
	
	vector<vector<F>> input(vectors);
	for(int i = 0; i < vectors; i++){
		input[i].resize(buff1.size()/vectors);
		for(int j = 0; j < input[i].size(); j++){
			input[i][j] = buff1[i*input[i].size() + j];
		}
	}
	buff1.clear();
	vector<F>(buff1).swap(buff1);

	mul_tree_proof P1 = prove_multiplication_tree_new(input,previous_r,prev_x,vt,ps);
	for(int i = 0; i < input.size(); i++){
		input[i].clear();
		vector<F>(input[i]).swap(input[i]);		
	}
	input.clear();
	vector<vector<F>>(input).swap(input);
	
	if(fd.name == "wiring_consistency_check"){
		F prod_r = F(1),prod_w = F(1),prod_i = P1.output[6],prod_f = P1.output[7];
		for(int i = 0; i < 3; i++){
			prod_r *= P1.output[i];
			prod_w *= P1.output[i+3];
		}
		if(prod_r*prod_f != prod_w*prod_i){
			printf("Error in output\n");
			exit(-1);
		}
	}else if(fd.name == "wiring_consistency_check_opt"){
		F prod_r = F(1),prod_w = F(1),prod_i = P1.output[3],prod_f = P1.output[7];
		for(int i = 0; i < 3; i++){
			prod_r *= P1.output[i];
			prod_w *= P1.output[i+4];
		}
		if(prod_r*prod_f != prod_w*prod_i){
			printf("Error in output\n");
			exit(-1);
		}
	}
	
	//exit(-1);
	reset_stream(fd);
	if(layers == 0){
		return P1.output;
	}else if(layers <= distance || naive){
	
		vector<F> old_claims(1); old_claims[0] = P1.final_eval;
		vector<F> new_claims(1);
		vector<vector<F>> new_r,old_r(1);old_r[0] = P1.individual_randomness;
		old_r[0].insert(old_r[0].end(),P1.global_randomness.begin(),P1.global_randomness.end());
		
		for(int i = layers-1; i >= 0; i--){
			printf("OK %d\n",i);
			if(fd.name == "wiring_consistency_check"){
				generate_3product_sumcheck_beta_stream_batch(fd, old_r, 1, 1, i, old_claims, new_claims, new_r, vt, ps);
			}else{
				generate_3product_sumcheck_beta_stream_batch_optimized(fd, old_r, 1, 1, i, old_claims, new_claims, new_r, vt, ps);
			}
			old_claims = new_claims;
			old_r = new_r;
		}
	}else{
		int batches = layers/distance;
		
		vector<vector<F>> new_r, old_r(batches);
		vector<F> r_temp = generate_randomness((int)log2(size*vectors/(1ULL<<distance))- P1.global_randomness.size()-P1.individual_randomness.size());

		
		r_temp.insert(r_temp.begin(),P1.global_randomness.begin(),P1.global_randomness.end());
		r_temp.insert(r_temp.begin(),P1.individual_randomness.begin(),P1.individual_randomness.end());
		for(int i = 0; i < old_r.size(); i++){
			old_r[i] = r_temp;
		}
		vector<F> old_claims,new_claims(batches,F(0));
		if(fd.name == "wiring_consistency_check"){
			generate_claims(fd, old_r[0], old_claims, batches , distance-1, distance);
		}else{
			generate_claims_opt(fd, old_r[0], old_claims, batches , distance-1, distance);
		}
		for(int i = distance-1; i >= 0; i--){
			printf("~OK %d\n",i);
			if(fd.name == "wiring_consistency_check"){
				generate_3product_sumcheck_beta_stream_batch(fd, old_r, 1, 1, i, old_claims, new_claims, new_r, vt, ps);
			}else{
				generate_3product_sumcheck_beta_stream_batch_optimized(fd, old_r, batches,distance , i, old_claims, new_claims, new_r, vt, ps);
			}
			old_claims = new_claims;
			old_r = new_r;
			/*
			if(i > 0){
				//generate_claims(fd, old_r, old_claims, batches , i-1, distance);
				for(int j = 0; j < old_claims.size(); j++){
					if(old_claims[j] != new_claims[j]){
						printf(">>>> %d\n",j);
					}
				}
			}*/
		}

	}
	if(!naive){
		open_layers( fd_com ,MT_hashes,vt,ps);
	}
	return P1.output;
	
}


void _generate_3product_sumcheck_proof_folded(F* v1, F* v2, F* v3,F* new_v1,F* new_v2,F* new_v3, cubic_poly &poly,F sum, F rand, int idx, int L ){
	
 	int size = L/threads;
	int pos = idx*size;
	linear_poly l1,l2,l3;
	
	cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
	for(int j = pos; j < pos+size; j++){
		if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			//q1 = quadratic_poly()
			F coef = v2[2*j+1] - v2[2*j];
			l2 = linear_poly(coef,v2[2*j]);
			l3 = linear_poly(-coef,sum - v2[2*j]);
			//l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
			temp_poly = l1*l2*l3;
			poly = poly + temp_poly;
		}
		new_v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
		new_v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
		new_v3[j] = sum - new_v2[j];
	}
}


void _generate_3product_sumcheck(F* v1,F* v2,F* v3,F* new_v1,F* new_v2, F* new_v3, cubic_poly &poly, F rand, int idx, int L){
	int size = L/threads;
	int pos = idx*size;
	linear_poly l1,l2,l3;
	cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);

	

	for(int j = pos; j < pos+size; j++){
		if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			//q1 = quadratic_poly()
			F coef = v2[2*j+1] - v2[2*j];
			l2 = linear_poly(coef,v2[2*j]);
			l3 = linear_poly(-coef,F(1) - v2[2*j]);
			temp_poly = l1*l2*l3;
			poly = poly + temp_poly;
		}
		new_v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
		if(v2[2*j] == F(0) && v2[2*j+1] == F(0)){
			new_v2[j] = F(0);
			new_v3[j] = F(1);
		}else{
			new_v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
			new_v3[j] = F(1)-new_v2[j];//(1-r[i])*v3[2*j] + r[i]*v3[2*j+1];	

		}
	}
}


struct proof _generate_3product_sumcheck_proof(vector<F> &v1, vector<F> &v2, vector<F> &v3,F previous_r, double &vt, double &ps){
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(v1.size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;
	for(int i = 0; i < rounds; i++){
		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3;
			
			int L = 1 << (rounds -1- i);
			for(int j = 0; j < L; j++){
				if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
					l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
					//q1 = quadratic_poly()
					F coef = v2[2*j+1] - v2[2*j];
					l2 = linear_poly(coef,v2[2*j]);
					coef = v3[2*j+1] - v3[2*j];
					l3 = linear_poly(coef,v3[2*j]);
					temp_poly = l1*l2*l3;
					poly = poly + temp_poly;

				}
				if(v1[2*j+1] == F(0) && v1[2*j] == F(0)){
					v1[j] = F(0);
				}else{
					F v = rand*(v1[2*j+1] - v1[2*j]);
					v1[j] = v1[2*j] + v;//(F(1)-rand)*v1[2*j] + rand*v1[2*j+1];
				}
				if(v2[2*j + 1] == F(0) && v2[2*j] == F(0)){
					v2[j] = F(0);
				}else{
					F v = rand*(v2[2*j+1] - v2[2*j]);
					v2[j] = v2[2*j] + v;
				}
				F v = rand*(v3[2*j+1] - v3[2*j]);
				v3[j] = v3[2*j] + v;

			}

		r.push_back(rand);
		vector<F> input;
		
		//input.push_back(rand);
		//input.push_back(poly.a);
		//input.push_back(poly.b);
		//input.push_back(poly.c);
		//input.push_back(poly.d);
		clock_t s,e;
		s = clock();
		rand = mimc_hash(rand,poly.a);
		rand = mimc_hash(rand,poly.b);
		rand = mimc_hash(rand,poly.c);
		rand = mimc_hash(rand,poly.d);
		e = clock();
		ps += 5*sizeof(F)/1024.0;
		vt += (double)(e-s)/(double)CLOCKS_PER_SEC;
		
		//vector<vector<F>> temp = mimc_multihash3(input);
		//Pr.w_hashes.push_back(temp);
		
		//rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		p.push_back(poly);
	}

	clock_t s,e;
	s = clock();
	rand = mimc_hash(rand,v1[0]);
	rand = mimc_hash(rand,v2[0]);
	//rand = mimc_hash(rand,v3[0]);
	e = clock();
	ps += 3*sizeof(F)/1024.0;
	vt += (double)(e-s)/(double)CLOCKS_PER_SEC;
		
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = rand;
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v3[0]);
	return Pr;
}

struct proof _generate_batch_3product_sumcheck_proof(vector<vector<F>> &v1, vector<vector<F>> &v2, vector<F> &v3,vector<F> a,F previous_r){
	struct proof Pr;
	int rounds = int(log2(v1[0].size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;
	quadratic_poly temp_qpoly;
	cubic_poly temp_poly;
	cubic_poly total;
	vector<cubic_poly> poly(v1.size());
	vector<int> sizes(v1.size());
	for(int i = 0; i < sizes.size(); i++){
		sizes[i] = v1[i].size();
	}
	vector<F> evaluations(2*v1.size()+1,F(0));
	
	for(int i = 0; i < rounds; i++){
		total = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		for(int k = 0; k < v1.size(); k++){
			poly[k] = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		} 
		vector<linear_poly> l1(v1.size()),l2(v2.size()),l3(v3.size());
		for(int k = 0; k < sizes.size(); k++){
			sizes[k] = sizes[k]/2;
		}	
		int L = 1 << (rounds -1- i);
		for(int j = 0; j < L; j++){
			for(int k = 0; k < v1.size(); k++){
				
				if(sizes[k] == 0 && j == 0){
					if(evaluations[2*k+1] == F(0)){
						evaluations[2*k+1] = v1[k][0];
						evaluations[2*k+2] = v2[k][0];
					}
					l1[k] = linear_poly(F_ZERO - v1[k][0],v1[k][0]);
					l2[k] = linear_poly(F_ZERO - v2[k][0],v2[k][0]);
					temp_poly = l1[k]*l2[k]*l3[0];
					poly[k] = poly[k] + temp_poly;
					v1[k][0] = v1[k][2*j] - rand*(v1[k][2*j]); 
					v2[k][0] = v2[k][2*j] - rand*(v2[k][2*j]); 
					continue;
				}
				
				if(sizes[k] <= j)continue;

				l1[k] = linear_poly(v1[k][2*j+1] - v1[k][2*j],v1[k][2*j]);
				l2[k] = linear_poly(v2[k][2*j+1] - v2[k][2*j],v2[k][2*j]);
				
				if(k == 0){
					l3[k] = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
				}
				temp_poly = l1[k]*l2[k]*l3[0];
				poly[k] = poly[k] + temp_poly;

				v1[k][j] = v1[k][2*j] + rand*(v1[k][2*j+1] - v1[k][2*j]); 
				v2[k][j] = v2[k][2*j] + rand*(v2[k][2*j+1] - v2[k][2*j]); 
				if(k == 0){
					v3[j] = v3[2*j] + rand*(v3[2*j+1] - v3[2*j]); 
				}	
			}
		}
		r.push_back(rand);
		vector<F> input;
		for(int k = 0; k < v1.size(); k++){
			total.a += a[k]*poly[k].a;
			total.b += a[k]*poly[k].b;
			total.c += a[k]*poly[k].c;
			total.d += a[k]*poly[k].d;
		}
		
		rand = mimc_hash(rand,total.a);
		rand = mimc_hash(rand,total.b);
		rand = mimc_hash(rand,total.c);
		rand = mimc_hash(rand,total.d);


		//rand = mimc_multihash(input);
		p.push_back(total);
	}
	for(int k = 0; k < v1.size(); k++){
		rand = mimc_hash(rand,v1[k][0]);
		rand = mimc_hash(rand,v2[k][0]);
		if(k == 0){
			rand = mimc_hash(rand,v3[0]);
		}
	}
	//rand = mimc_hash(rand,v3[0]);
	
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = rand;
	evaluations[0] = v3[0];
	for(int k = 0; k < v1.size(); k++){
		if(evaluations[2*k+1] == 0){
			evaluations[2*k+1] = v1[k][0];
			evaluations[2*k+2] = v2[k][0];
		}
	}
	for(int k = 0; k < v1.size(); k++){
		if(k == 0){
			Pr.vr.push_back(v3[0]);
		}
		Pr.vr.push_back(v1[k][0]);Pr.vr.push_back(v2[k][0]);
	}
	for(int k = 1; k < evaluations.size(); k++){
		Pr.vr.push_back(evaluations[k]);
	}

	return Pr;
}

struct proof generate_batch_3product_sumcheck_proof(vector<vector<F>> &v1, vector<vector<F>> &v2, vector<vector<F>> &v3,vector<F> a,F previous_r){
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(v1[0].size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;
	quadratic_poly temp_qpoly;
	cubic_poly temp_poly;
	cubic_poly total;
	vector<cubic_poly> poly(v1.size());
	for(int i = 0; i < rounds; i++){
		total = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		for(int k = 0; k < v1.size(); k++){
			poly[k] = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		} 
		vector<linear_poly> l1(v1.size()),l2(v2.size()),l3(v3.size());
			
		int L = 1 << (rounds -1- i);
		for(int j = 0; j < L; j++){
			for(int k = 0; k < v1.size(); k++){
				//printf("OK %d\n",k);			
				l1[k] = linear_poly(v1[k][2*j+1] - v1[k][2*j],v1[k][2*j]);
				//q1 = quadratic_poly()
				l2[k] = linear_poly(v2[k][2*j+1] - v2[k][2*j],v2[k][2*j]);
				if(k < v3.size()){
					l3[k] = linear_poly(v3[k][2*j+1] - v3[k][2*j],v3[k][2*j]);
					temp_poly = l1[k]*l2[k]*l3[k];
					poly[k] = poly[k] + temp_poly;
				}else{
					temp_qpoly = l1[k]*l2[k];
					poly[k].b = poly[k].b + temp_qpoly.a;
					poly[k].c = poly[k].c + temp_qpoly.b;
					poly[k].d = poly[k].d + temp_qpoly.c;
				}
			
				v1[k][j] = v1[k][2*j] + rand*(v1[k][2*j+1] - v1[k][2*j]); 
				v2[k][j] = v2[k][2*j] + rand*(v2[k][2*j+1] - v2[k][2*j]); 
				if(k < v3.size()){
					v3[k][j] = v3[k][2*j] + rand*(v3[k][2*j+1] - v3[k][2*j]); 
				}
				
			}
				
			
		}
		r.push_back(rand);
		vector<F> input;
		for(int k = 0; k < v3.size(); k++){
			total.a += a[k]*poly[k].a;
			total.b += a[k]*poly[k].b;
			total.c += a[k]*poly[k].c;
			total.d += a[k]*poly[k].d;
		}
		for(int k = v3.size(); k < v1.size(); k++){
			total.b += a[k]*poly[k].b;
			total.c += a[k]*poly[k].c;
			total.d += a[k]*poly[k].d;
			
		}
		rand = mimc_hash(rand,total.a);
		rand = mimc_hash(rand,total.b);
		rand = mimc_hash(rand,total.c);
		rand = mimc_hash(rand,total.d);


		//rand = mimc_multihash(input);
		p.push_back(total);
	}
	for(int k = 0; k < v1.size(); k++){
		rand = mimc_hash(rand,v1[k][0]);
		rand = mimc_hash(rand,v2[k][0]);
		if(k < v3.size()){
			rand = mimc_hash(rand,v3[k][0]);
		}
	}
	//rand = mimc_hash(rand,v3[0]);
	
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = rand;
	for(int k = 0; k < v1.size(); k++){
		Pr.vr.push_back(v1[k][0]);Pr.vr.push_back(v2[k][0]);
		if(k < v3.size()){
			Pr.vr.push_back(v3[k][0]);
		}
	}

	return Pr;
}

struct proof generate_3product_sumcheck_proof(vector<F> &v1, vector<F> &v2, vector<F> &_v3,F previous_r){
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(v1.size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;
	//F *v3 = _v3.data();
	F *v3 = (F *)malloc(v2.size()/2 * sizeof(F));
	for(int i = 0; i < rounds; i++){
		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		if(threads == 1  || 1 << (rounds - 1-i) <= 1<<10){
			cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3;
			
			int L = 1 << (rounds -1- i);
			for(int j = 0; j < L; j++){
				if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
					l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
					//q1 = quadratic_poly()
					F coef = v2[2*j+1] - v2[2*j];
					l2 = linear_poly(coef,v2[2*j]);
					l3 = linear_poly(-coef,F(1) - v2[2*j]);
					temp_poly = l1*l2*l3;
					poly = poly + temp_poly;

				}
				v1[j] = (F(1)-rand)*v1[2*j] + rand*v1[2*j+1];
				if(v2[2*j] == F(0) && v2[2*j+1] == F(0)){
					v2[j] = F(0);
					v3[j] = F(1);
				}else{
					v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
					v3[j] = F(1)-v2[j];//(1-r[i])*v3[2*j] + r[i]*v3[2*j+1];	

				}
			}

		}
		r.push_back(rand);
		vector<F> input;
		
		//input.push_back(rand);
		//input.push_back(poly.a);
		//input.push_back(poly.b);
		//input.push_back(poly.c);
		//input.push_back(poly.d);
		//vector<vector<F>> temp = mimc_multihash3(input);
		//Pr.w_hashes.push_back(temp);
		//rand = temp[temp.size()-1][temp[0].size()-1];
		rand = mimc_hash(rand,poly.a);
		rand = mimc_hash(rand,poly.b);
		rand = mimc_hash(rand,poly.c);
		rand = mimc_hash(rand,poly.d);


		//rand = mimc_multihash(input);
		p.push_back(poly);
	}
	rand = mimc_hash(rand,v2[0]);
	rand = mimc_hash(rand,v1[0]);
	//rand = mimc_hash(rand,v3[0]);
	
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = rand;
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v3[0]);
	free(v3);
	
	return Pr;
}

void _generate_norm_sumcheck_proof(F **M,F **temp_M,vector<vector<F>> &_M, vector<F> &beta, quadratic_poly &poly, F rand,int idx, int L,int i ){
	int size = _M.size()/threads;
	int pos = idx*size;
	quadratic_poly temp_poly;
	
	for(int k = pos; k < size+pos; k++){
		temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		for(int j = 0; j < L; j++){
			if(i == 0){
				F diff = _M[k][2*j + 1] - _M[k][2*j];
				temp_poly = temp_poly + quadratic_poly(diff*diff,F(2)*diff*_M[k][2*j],_M[k][2*j]*_M[k][2*j]);
				temp_M[k][j] = _M[k][2*j] + rand*(diff);			
			}else{
				F diff = M[k][2*j + 1] - M[k][2*j];
				temp_poly = temp_poly + quadratic_poly(diff*diff,F(2)*diff*M[k][2*j],M[k][2*j]*M[k][2*j]);
				temp_M[k][j] = M[k][2*j] + rand*(diff);	
			}

		}
		poly = poly +  quadratic_poly(beta[k] * temp_poly.a,beta[k] * temp_poly.b,beta[k] * temp_poly.c);
	}
}




void _generate_2product_sumcheck(F *v1,vector<F> &_v1, F *v2, vector<F> &_v2,F *new_v1,F *new_v2,quadratic_poly &poly,F rand,int idx,int L,int i){
	
	int size = L/threads;
	
	int pos = idx*size;
	
	linear_poly l1,l2;
	quadratic_poly temp_poly;
	for(int j = pos; j < pos + size; j++){
		if(i == 0){
			l1 = linear_poly(_v1[2*j+1] - _v1[2*j],_v1[2*j]);
			l2 = linear_poly(_v2[2*j+1] - _v2[2*j],_v2[2*j]);
			temp_poly = l1*l2;
			poly = poly + temp_poly;
			new_v1[j] = _v1[2*j] + rand*(_v1[2*j+1]-_v1[2*j]);
			new_v2[j] = _v2[2*j] + rand*(_v2[2*j+1]-_v2[2*j]);
		
		}else{
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
			temp_poly = l1*l2;
			poly = poly + temp_poly;
			new_v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
			new_v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
		}
		
	}
}

struct proof generate_2product_sumcheck_proof(vector<F> &_v1, vector<F> &_v2, F previous_r, double &vt, double &ps){
	struct proof Pr;
	vector<F> r;// = generate_randomness(int(log2(v1.size())));
	F rand = previous_r;
	vector<quadratic_poly> p;
	int rounds = int(log2(_v1.size()));
	
	F *v1 = (F *)malloc(_v1.size()*sizeof(F)/2);
	F *v2 = (F *)malloc(_v2.size()*sizeof(F)/2);
	clock_t t1,t2;
	for(int i = 0; i < rounds; i++){
		quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		
        quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		linear_poly l1,l2;
		int L = 1 << (rounds - 1-i);
		for(int j = 0; j < L; j++){
			if(i== 0){
				l1 = linear_poly(_v1[2*j+1] - _v1[2*j],_v1[2*j]);
				l2 = linear_poly(_v2[2*j+1] - _v2[2*j],_v2[2*j]);
				temp_poly = l1*l2;
				poly = poly + temp_poly;
			}else{
				l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
				l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
				temp_poly = l1*l2;
				poly = poly + temp_poly;
			}
		}
		clock_t t1,t2;
		t1 = clock();
		rand = mimc_hash(rand,poly.a);
		rand = mimc_hash(rand,poly.b);
		rand = mimc_hash(rand,poly.c);
		r.push_back(rand);	
		p.push_back(poly);
		poly.eval(rand);
		poly.eval(F(1)) + poly.eval(F(0));
		t2 = clock();
		vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
		ps += 3*sizeof(F)/1024.0;
		sc_vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
		for(int j = 0; j < L; j++){
			if(i == 0){
				v1[j] = _v1[2*j] + rand*(_v1[2*j+1]-_v1[2*j]);
				v2[j] = _v2[2*j] + rand*(_v2[2*j+1]-_v2[2*j]);					
			
			}else{
				v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
				v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);					
			}
		}
	}
    t1 = clock();	    
	rand = mimc_hash(rand,v1[0]);
	rand = mimc_hash(rand,v2[0]);
	t2 = clock();
	vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	ps += 2*sizeof(F)/1024.0;
		
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v2[0]);
	Pr.q_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = rand;
	free(v1);
	free(v2);
	
	return Pr;
 }




int generate_encoding_transcript(encoding_transcript &transcript ,const F *src, F *dst, long long n, int dep = 0)
{
    if(!__encode_initialized_proof)
    {
        __encode_initialized_proof = true;
        for(int i = 0; (n >> i) > 1; ++i)
        {
            scratch_proof[0][i] = new F[2 * n >> i];
            scratch_proof[1][i] = new F[2 * n >> i];
            scratch_size_proof[i] = (2 * n >> i);
        }
    }
    if(n <= distance_threshold)
    {
        for(long long i = 0; i < n; ++i)
            dst[i] = src[i];
        return n;
    }
    
    for(long long i = 0; i < n; ++i)
    {
        scratch_proof[0][dep][i] = src[i];
    }
    long long R = alpha * n;
    for(long long j = 0; j < R; ++j)
        scratch_proof[1][dep][j] = F(0ULL);
    //expander mult
   
    for(long long i = 0; i < n; ++i)
    {
        const F &val = src[i];
        for(int d = 0; d < _C[dep].degree; ++d)
        {
            int target = _C[dep].neighbor[i][d];
            scratch_proof[1][dep][target] = scratch_proof[1][dep][target] + _C[dep].weight[i][d] * val;
        }
    }
    vector<F> arr(R);
    for(int i = 0; i < R; i++){
        arr[i] = scratch_proof[1][dep][i];
    }
    transcript.x1.push_back(arr);
    vector<F>().swap(arr);
    arr.clear();

    
	long long L = generate_encoding_transcript(transcript,scratch_proof[1][dep], &scratch_proof[0][dep][n], R, dep + 1);
    
	//printf("%d - %d\n",n,n+L);
    assert(D[dep].L = L);
    R = D[dep].R;
    for(long long i = 0; i < R; ++i)
    {
        scratch_proof[0][dep][n + L + i] = F(0ULL);
    }
    
	arr.resize(L);
	for(int i = 0; i < L; i++){
		arr[i] = scratch_proof[0][dep][n + i];
	}
	transcript.x2_inp.push_back(arr);
	vector<F>().swap(arr);
    arr.clear();


    for(long long i = 0; i < L; ++i)
    {
        F &val = scratch_proof[0][dep][n + i];
        for(int d = 0; d < D[dep].degree; ++d)
        {
            long long target = D[dep].neighbor[i][d];
            scratch_proof[0][dep][n + L + target] = scratch_proof[0][dep][n + L + target] + val * D[dep].weight[i][d];
        }
    }
    
	arr.resize(R);
    for(int i = 0; i < R; i++){
        arr[i] = scratch_proof[0][dep][n + L + i];
    }
    transcript.x2.push_back(arr);
    vector<F>().swap(arr);
    arr.clear();
    
	
    for(long long i = 0; i < n + L + R; ++i)
    {
        dst[i] = scratch_proof[0][dep][i];
    }
	delete scratch_proof[0][dep];
	delete scratch_proof[1][dep];
	
    return n + L + R;
}

void generate_GKR_input(vector<F> &input, vector<F> &accesses1, vector<F> &accesses2, vector<F> &read_tr,vector<int> &access_idx1,
 vector<int> &access_idx2, vector<F> &beta1, vector<F> &beta2, vector<F> &weight){
	input.resize(5*access_idx1.size() + read_tr.size()/2 + 3*beta1.size()+2*beta2.size()+4);
	int counter = 0;
	for(int i  = 0; i < access_idx1.size(); i++){
		input[counter++] = access_idx1[i];
		input[counter++] = read_tr[4*i];
		input[counter++] = access_idx2[i];
		input[counter++] = read_tr[4*i+2];
		input[counter++] = weight[i];
	}
	for(int i = 0; i < beta1.size(); i++){
		input[counter++] = accesses1[i];
	}
	for(int i = 0; i < beta2.size(); i++){
		input[counter++] = accesses2[i];
	}

	for(int i = 0; i < read_tr.size()/4; i++){
		input[counter++] = read_tr[4*i+1];
		input[counter++] = read_tr[4*i+3];
	}
	for(int i = 0; i < beta1.size(); i++){
		input[counter++] = i;
	}
	for(int i = 0; i < beta1.size(); i++){
		input[counter++] = beta1[i];
	}
	
	for(int i = 0; i < beta2.size(); i++){
		input[counter++] = beta2[i];
	}

	input[counter++] = F(0);
	input[counter++] = F(1);
    input[counter++] = random();
    input[counter++] = random();
	//printf("%d,%d\n",input.size(),counter);
}


int generate_read_transcript(vector<F> &accesses1, vector<F> &accesses2, vector<F> &read_tr,vector<int> &access_idx1,
 vector<int> &access_idx2, vector<F> &beta1, vector<F> &beta2){
	
	if(accesses1.size() == 0){
		accesses1.resize(beta1.size(),F(0));
		accesses2.resize(beta2.size(),F(0));
	}
	if(read_tr.size() == 0){
		read_tr.resize(access_idx1.size()*4);
	}
	
	for(int i = 0; i < access_idx1.size(); i++){
		read_tr[4*i] = accesses1[access_idx1[i]]+1;
        read_tr[4*i+1] = beta1[access_idx1[i]];
        read_tr[4*i+2] = accesses2[access_idx2[i]]+1;
        read_tr[4*i+3] = beta2[access_idx2[i]];
        accesses1[access_idx1[i]] += F(1);
		accesses2[access_idx2[i]]+=F(1);
	}

}

int generate_access_idx(vector<int> &access_idx1, vector<int> &access_idx2, vector<F> &weight, int Offset, int n, int dep, int &lvl){
	long long R = alpha * n;
    
	F zero = F(0);
	if(n <= distance_threshold)
    {
        return n;
    }
	vector<F> buff(n,zero);
	
	for(long long i = 0; i < n; ++i){
        for(int d = 0; d < _C[dep].degree; ++d){
            int target = (_C[dep].neighbor[i][d]+lvl);
			access_idx1.push_back(target);
			access_idx2.push_back(i + Offset);
			weight.push_back(_C[dep].weight[i][d]);
        }
	
	}
	for(int i = 0; i < R; i++){
		access_idx1.push_back(lvl+i);
		access_idx2.push_back(i + Offset + n);
		weight.push_back(F(-1));
	}
	int l= lvl+R;
	long long L = generate_access_idx(access_idx1,access_idx2,weight, Offset+n,R, dep + 1,l);
	
	R = D[dep].R;
   
	for(long long i = 0; i < L; ++i)
    {
        for(int d = 0; d < D[dep].degree; ++d)
        {
            long long target = D[dep].neighbor[i][d] + lvl;
			access_idx1.push_back(target);
			access_idx2.push_back(i + Offset+n);
			weight.push_back(D[dep].weight[i][d]);
        }
    }
	for(int i = 0; i < R; i++){
		access_idx1.push_back(i+ lvl);
		access_idx2.push_back(i+ Offset +n+ L);
		weight.push_back(F(-1));
	}
	lvl += R;
	return	n + L + R;
	
}

void commit_parity_matrix(int n){
	vector<int> access_idx1,access_idx2;
	vector<F> weight,accesses1,accesses2;
	int lvl = 0;
	
	generate_access_idx(access_idx1, access_idx2, weight, 0, n, 0, lvl);	
	accesses1.resize(2*n,F(0));
	accesses2.resize(2*n,F(0));
	
	vector<F> access_counter1(access_idx1.size()),access_counter2(access_idx2.size());
	
	for(int i = 0; i < access_idx1.size(); i++){
		access_counter1[i] = accesses1[access_idx1[i]]+1;
        access_counter2[i] = accesses2[access_idx2[i]]+1;
        accesses1[access_idx1[i]] += F(1);
		accesses2[access_idx2[i]]+=F(1);
	}
	pad_vector(access_counter1);
	pad_vector(access_counter2);
	pad_vector(weight);
	
	vector<F> public_witness(2*access_counter1.size(),F(0));
	for(int i = 0; i < access_idx1.size(); i++){
		public_witness[i] = access_idx1[i];
	}
	for(int i = 0; i < access_idx1.size(); i++){
		public_witness[i + access_idx1.size()] = access_idx2[i];
	}
	public_witness.insert(public_witness.end(),access_counter1.begin(),access_counter1.end());
	public_witness.insert(public_witness.end(),access_counter2.begin(),access_counter2.end());
	public_witness.insert(public_witness.end(),weight.begin(),weight.end());
	public_witness.insert(public_witness.end(),accesses1.begin(),accesses1.end());
	public_witness.insert(public_witness.end(),accesses2.begin(),accesses2.end());
	pad_vector(public_witness);
	C_p = shockwave_commit(public_witness,16);
}

void open_parity_matrix(vector<F> r1, vector<F> r2, int n, double &vt, double &ps){
	vector<int> access_idx1,access_idx2;
	vector<F> weight,accesses1,accesses2,read_tr,beta1,beta2,input;
	vector<F> buff1;
	shockwave_data *C_w;
	int lvl = 0;

	precompute_beta(r1,beta1);
	precompute_beta(r2,beta2);
	
	generate_access_idx(access_idx1, access_idx2, weight, 0, n, 0, lvl);	
	generate_read_transcript(accesses1, accesses2, read_tr, access_idx1, 
	access_idx2, beta1, beta2);

	
	
	vector<F> access_counter1(access_idx1.size()),access_counter2(access_idx2.size());
	vector<F> betas1(access_idx1.size()),betas2(access_idx2.size());
	
	for(int i  = 0; i < access_counter1.size(); i++){
		access_counter1[i] = read_tr[4*i];
		access_counter2[i] = read_tr[4*i+2];
	}
	for(int i = 0; i <  access_counter1.size(); i++){
		betas1[i] = read_tr[4*i+1];
		betas2[i] = read_tr[4*i+3];
	}
	
	pad_vector(access_counter1);
	pad_vector(access_counter2);
	pad_vector(betas1);
	pad_vector(betas2);
	buff1 = betas1;
	buff1.insert(buff1.end(),betas2.begin(),betas2.end());
	C_w = shockwave_commit(buff1,16);
	buff1.clear();
	//pad_vector(access_idx1);
	//pad_vector(access_idx2);
	
	
	F a = random();
	F b = random();

	vector<vector<F>> mul_tree_input(4);
	mul_tree_input[0].resize(access_counter1.size());
	mul_tree_input[1].resize(access_counter1.size());
	mul_tree_input[2].resize(access_counter2.size());
	mul_tree_input[3].resize(access_counter2.size());
	for(int i = 0; i < mul_tree_input[0].size(); i++){
		mul_tree_input[0][i] = a*access_idx1[i] + b*(access_counter1[i]-F(1)) + betas1[i] + F(1);
		mul_tree_input[1][i] = a*access_idx1[i] + b*access_counter1[i] + betas1[i]+ F(1);
	}
	for(int i = 0; i < mul_tree_input[2].size(); i++){
		mul_tree_input[2][i] = a*access_idx2[i] + b*(access_counter2[i]-F(1)) + betas2[i]+ F(1);
		mul_tree_input[3][i] = a*access_idx2[i] + b*access_counter2[i] + betas2[i]+ F(1);
	}
	//generate_GKR_input(input, accesses1, accesses2, read_tr, access_idx1, access_idx2, beta1, beta2, weight);
	vector<F> prev_x;
	
	mul_tree_proof P1 = prove_multiplication_tree_new(mul_tree_input,F(21),prev_x,vt,ps);
	precompute_beta(P1.individual_randomness,buff1);
	
	vector<F> partial_y1(6,F(0)),partial_y2;
	F access_betas1_y = F(0),access_betas2_y = F(0);
	for(int i = 0; i < access_idx1.size(); i++){
		partial_y1[0] += buff1[i]*access_idx1[i];
		partial_y1[1] += buff1[i]*access_idx2[i];
		partial_y1[2] += buff1[i]*access_counter1[i];
		partial_y1[3] += buff1[i]*access_counter2[i];
		partial_y1[4] += buff1[i]*weight[i];
		access_betas1_y += buff1[i]*betas1[i];
		access_betas2_y += buff1[i]*betas2[i];
	}
	
	mul_tree_input[0].resize(beta1.size());
	mul_tree_input[1].resize(beta1.size());
	mul_tree_input[2].resize(beta2.size());
	mul_tree_input[3].resize(beta2.size());
	
	
	for(int i = 0; i < beta1.size(); i++){
		mul_tree_input[0][i] = a*F(i) + beta1[i] + F(1);
		mul_tree_input[1][i] = b*accesses1[i] + a*F(i) + beta1[i] + F(1);
	}
	for(int i = 0; i < beta2.size(); i++){
		mul_tree_input[2][i] = a*F(i) + beta2[i] + F(1);
		mul_tree_input[3][i] = b*accesses2[i] + a*F(i) + beta2[i] + F(1);
	}
	prove_multiplication_tree_new(mul_tree_input,F(21),prev_x,vt,ps);
	
	pad_vector(accesses1);
	pad_vector(accesses2);
	vector<F> final_r,remaining_r;
	for(int i = 0; i < (int)log2(accesses1.size()); i++){
		final_r.push_back(P1.individual_randomness[i]);
	}
	for(int i = (int)log2(accesses1.size()); i < P1.individual_randomness.size(); i++){
		remaining_r.push_back(P1.individual_randomness[i]);
	}

	F accesses1_y = evaluate_vector(accesses1,final_r);
	F accesses2_y = evaluate_vector(accesses2,final_r);
	partial_y1[5] = accesses1_y*(F(1) - remaining_r[0]) + accesses2_y*remaining_r[0];
	for(int i = 1; i < remaining_r.size(); i++){
		partial_y1[5] *= (F(1)-remaining_r[i]);
	}
	pad_vector(weight);
	pad_vector(betas1);
	pad_vector(betas2);
	buff1 = weight;
	vector<F> buff2 = betas1,buff3 = betas2;
	proof P2 = _generate_3product_sumcheck_proof(buff1,buff2,buff3,F(321),vt,ps);
	
	// Reduce evaluations
	F r = random(),_a = random();
	F y1 = (F(1)-r)*access_betas1_y + r*access_betas2_y;
	F y2 = (F(1) - r)*P2.vr[1] + r*P2.vr[2];
	buff1 = betas1; buff1.insert(buff1.end(),betas2.begin(),betas2.end());
	buff2.clear();buff3.clear();
	vector<F> r_aggr = P1.individual_randomness;r_aggr.push_back(r);
	
	precompute_beta(r_aggr,buff2);
	r_aggr = P2.randomness[0];r_aggr.push_back(r);
	precompute_beta(r_aggr,buff3);
	for(int i = 0; i < buff2.size(); i++){
		buff2[i] += _a*buff3[i];
	}
	
	
	proof P3 = generate_2product_sumcheck_proof(buff2,buff1,F(321),vt,ps);
	if(P3.q_poly[0].eval(F(0)) + P3.q_poly[0].eval(F(1)) != y1 + _a*y2){
		printf("Error 1\n");
		exit(-1);
	}


	
	// Reduce evaluations of public witness
	vector<F> public_witness(2*access_counter1.size(),F(0));
	for(int i = 0; i < access_idx1.size(); i++){
		public_witness[i] = access_idx1[i];
	}
	for(int i = 0; i < access_idx2.size(); i++){
		public_witness[i+access_counter1.size()] = access_idx2[i];
	}
	public_witness.insert(public_witness.end(),access_counter1.begin(),access_counter1.end());
	public_witness.insert(public_witness.end(),access_counter2.begin(),access_counter2.end());
	public_witness.insert(public_witness.end(),weight.begin(),weight.end());
	public_witness.insert(public_witness.end(),accesses1.begin(),accesses1.end());
	public_witness.insert(public_witness.end(),accesses2.begin(),accesses2.end());
	pad_vector(public_witness);
	
	pad_vector(partial_y1);
	vector<F> aggr_r_pad = generate_randomness((int)log2(public_witness.size()) - P1.individual_randomness.size());
	r_aggr = P1.individual_randomness;r_aggr.insert(r_aggr.end(),aggr_r_pad.begin(),aggr_r_pad.end());
	y1 = evaluate_vector(partial_y1,aggr_r_pad);
	buff1.clear();buff2.clear();
	precompute_beta(r_aggr,buff1);
	y2 = P2.vr[0];
	r_aggr = P2.randomness[0];
	r_aggr.push_back(F(0));
	r_aggr.push_back(F(0));
	r_aggr.push_back(F(1));
	precompute_beta(r_aggr,buff2);
	for(int i = 0; i < buff2.size(); i++){
		buff1[i] += _a*buff2[i];
	}
	proof P4 = generate_2product_sumcheck_proof(buff1,public_witness,F(321),vt,ps);
	if(P4.q_poly[0].eval(F(0)) + P4.q_poly[0].eval(F(1)) != y1 + _a*y2){
		printf("Error 2\n");
		exit(-1);
	}

	shockwave_prove(C_p,P4.randomness[0],vt,ps);

	shockwave_prove(C_w,P3.randomness[0],vt,ps);

}


int evaluate_parity_matrix(vector<F> &A, vector<F> &beta1, int Offset, int n, int dep, int &lvl){
	long long R = alpha * n;
    F weight;
	F zero = F(0);
	if(n <= distance_threshold)
    {
        return n;
    }
	vector<F> buff(n,zero);
	
	for(long long i = 0; i < n; ++i){
        for(int d = 0; d < _C[dep].degree; ++d){
            int target = (_C[dep].neighbor[i][d]+lvl);
			A[i + Offset] += beta1[target]*_C[dep].weight[i][d];
        }
	
	}
	
	for(int i = 0; i < R; i++){
		A[i + Offset + n] -= beta1[lvl+i];
	}
	
	int l= lvl+R;
	long long L = evaluate_parity_matrix(A, beta1, Offset+n,R, dep + 1,l);
	
	R = D[dep].R;
   
	for(long long i = 0; i < L; ++i)
    {
        for(int d = 0; d < D[dep].degree; ++d)
        {
            long long target = D[dep].neighbor[i][d] + lvl;
			A[i + Offset+n] += beta1[target]*D[dep].weight[i][d];
        }
    }
	for(int i = 0; i < R; i++){
		A[i+ Offset +n+ L] -= beta1[i+ lvl];
	}
	lvl += R;
	return	n + L + R;
	
}
int evaluate_matrixes(vector<vector<F>> &A_vec, vector<vector<F>> &B_vec, vector<F> &beta1, vector<F> &beta2,long long n, int dep){
    
	long long R = alpha * n;
    F weight;
	F zero = F(0);
	if(n <= distance_threshold)
    {
        return n;
    }
	vector<F> buff(n,zero);
	
	for(long long i = 0; i < n; ++i){
        for(int d = 0; d < _C[dep].degree; ++d){
            int target = _C[dep].neighbor[i][d];
            int v1 = target%beta1.size();
			int v2 = target>>((int)log2(beta1.size()));
			buff[i] += beta1[v1]*beta2[v2]*_C[dep].weight[i][d];
        }
    }
	
	A_vec.push_back(buff);
	vector<F>().swap(buff);
	buff.clear();
	long long L = evaluate_matrixes(A_vec, B_vec, beta1, beta2,R, dep + 1);
	
	R = D[dep].R;
    srand(2*(666+dep));
	buff.resize(L,zero);
	 for(long long i = 0; i < L; ++i)
    {
        for(int d = 0; d < D[dep].degree; ++d)
        {
            long long target = D[dep].neighbor[i][d];
			int v1 = target%beta1.size();
			int v2 = target>>((int)log2(beta1.size()));
			buff[i] += beta1[v1]*beta2[v2]*D[dep].weight[i][d];
        }
    }
	B_vec.push_back(buff);
	vector<F>().swap(buff);
	buff.clear();
	return	n + L + R;

}

struct proof prove_fft(vector<F> &m, vector<F> r, F previous_sum, double &vt, double &ps){
	m.resize(2*m.size(),F(0));
	vector<F> FG(m.size(),F(0));
	
	phiGInit(FG,r.begin(),F(1),r.size(),false);
	struct proof Pr = generate_2product_sumcheck_proof(FG,m,r[r.size()-1],vt,ps);
	if(previous_sum != (Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1))){
		printf("Error in fft\n");
		//exit(-1);
	}
	Pr.randomness[0].pop_back();
	return Pr;
}

struct proof prove_fft_matrix(vector<vector<F>> M, vector<F> r, F previous_sum, double &vt, double &ps){
	
	for(int i  = 0; i < M.size(); i++){
		M[i].resize(2*M[i].size(),F(0));
	}
	
	vector<F> r1,r2;
	for(int i = 0; i < int(log2(M[0].size())); i++){
		r2.push_back(r[i]);
	}
	for(int i = 0; i < int(log2(M.size())); i++){
		r1.push_back(r[i+int(log2(M[0].size()))]);
	}
	clock_t start,end;
	start = clock();
	
	vector<F> arr = prepare_matrix(transpose(M),r1);
	
	
	
	vector<F> Fg1(M[0].size()); 
	phiGInit(Fg1,r2.begin(),F(1),r2.size(),false);
	struct proof Pr = generate_2product_sumcheck_proof(Fg1,arr,r[r.size()-1],vt,ps);
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;

	
	
	if(previous_sum != (Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1))){
		printf("Error in fft\n");
		exit(-1);
	}
	for(int i = 0; i < r1.size(); i++){
		Pr.randomness[0].push_back(r1[i]);
	}
	//Pr.randomness.push_back(r1); 
	//Pr.randomness.push_back(r2);
	return Pr;
}

struct proof prove_ifft_matrix(vector<vector<F>> M, vector<F> r, F previous_sum, double &vt, double &ps){
	F scale;
	scale = F(M[0].size()).inv();
	
	//F::inv(scale,M[0].size());
	vector<F> r1,r2;
	
	for(int i = 0; i < int(log2(M[0].size())); i++){
		r2.push_back(r[i]);
	}
	for(int i = 0; i < int(log2(M.size())); i++){
		r1.push_back(r[i+1+int(log2(M[0].size()))]);
	}
	
	vector<F> Fg(M[0].size());
	clock_t start,end;
	start = clock();
	vector<F> arr = prepare_matrix(transpose(M),r1);
	phiGInit(Fg,r2.begin(),scale,r2.size(),true);
	struct proof Pr = generate_2product_sumcheck_proof(Fg,arr,r[r.size()-1],vt,ps);
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;

	if(previous_sum != (F(1)-r[int(log2(M[0].size()))])*(Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1))){
		printf("Error in ifft\n");
		//exit(-1);
	}
	
	for(int i = 0; i < r1.size(); i++){
		Pr.randomness[0].push_back(r1[i]);
	}
	return Pr;
}



struct proof batch_sumcheck(vector<vector<F>> &arr, vector<vector<F>> &eval_A, vector<vector<F>> &eval_B, vector<F> evals){
	proof P;
	size_t L = 0;
	F rand = F(312);
	vector<size_t> len;
	for(int i = 0; i < arr.size(); i++){
		if(L < arr[i].size()) L = arr[i].size(); 
		len.push_back(arr[i].size());
	}

	int rounds = (int)log2(L);
	
	vector<F> a = generate_randomness(arr.size()); 
	vector<quadratic_poly> polynomials;
	vector<F> r;
	for(int i = 0; i < rounds; i++){
		quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		for(int j = 0; j < eval_A.size(); j++){
		
		
			quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			quadratic_poly p = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2;
			if((int)log2(arr[j].size()) - 1-i >= 0){
				L = 1 << ((int)log2(arr[j].size()) - 1-i);
			}else{
				L =  0;
			}
			
			if(L >= 1){
		
				for(int k = 0; k < L; k++){
					l1 = linear_poly(arr[j][2*k+1] - arr[j][2*k],arr[j][2*k]);
					l2 = linear_poly(eval_A[j][2*k+1] - eval_A[j][2*k],eval_A[j][2*k]);
					temp_poly = l1*l2;
					p = p + temp_poly;
				}
		
				
			}else{
				l1 = linear_poly(- arr[j][0],arr[j][0]);
				l2 = linear_poly(- eval_A[j][0],eval_A[j][0]);
				temp_poly = l1*l2;
				p = p + temp_poly;
			}
			p.a = a[j]*p.a;
			p.b = a[j]*p.b;
			p.c = a[j]*p.c;
			poly = poly + p;
		}
		for(int j = 0; j < eval_B.size(); j++){
			
			quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			quadratic_poly p = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2;
			if((int)log2(arr[j+eval_A.size()].size()) - 1-i >= 0){
				L = 1 << ((int)log2(arr[j+eval_A.size()].size()) - 1-i);
			}else{
				L = 0;
			}
			if(L >= 1){
				for(int k = 0; k < L; k++){
					l1 = linear_poly(arr[j+eval_A.size()][2*k+1] - arr[j+eval_A.size()][2*k],arr[j+eval_A.size()][2*k]);
					l2 = linear_poly(eval_B[j][2*k+1] - eval_B[j][2*k],eval_B[j][2*k]);
					temp_poly = l1*l2;
					p = p + temp_poly;
				}
			}else{
				l1 = linear_poly(- arr[j+eval_A.size()][0],arr[j+eval_A.size()][0]);
				l2 = linear_poly(- eval_B[j][0],eval_B[j][0]);
				temp_poly = l1*l2;	
				p = p + temp_poly;
			}
			p.a = a[j+eval_A.size()]*p.a;
			p.b = a[j+eval_A.size()]*p.b;
			p.c = a[j+eval_A.size()]*p.c;
			
			poly = poly + p;
		}
		rand = mimc_hash(rand,poly.a);
		rand = mimc_hash(rand,poly.b);
		rand = mimc_hash(rand,poly.c);
		r.push_back(rand);
		polynomials.push_back(poly);
		for(int j = 0; j < eval_A.size(); j++){
			if((int)log2(arr[j].size()) - 1-i >= 0){
				L = 1 << ((int)log2(arr[j].size()) - 1-i);
			}else{
				L = 0;
			}
			if(L >= 1){
				for(int k = 0; k < L; k++){
					arr[j][k] = arr[j][2*k] + rand*(arr[j][2*k+1]-arr[j][2*k]);
					eval_A[j][k] = eval_A[j][2*k] + rand*(eval_A[j][2*k+1]-eval_A[j][2*k]);						
				}
			}else{
				arr[j][0] = (F(1)-rand)*arr[j][0];
				eval_A[j][0] = (F(1)-rand)*eval_A[j][0];
			}
			
		}
		for(int j = 0; j < eval_B.size(); j++){
			if((int)log2(arr[j+eval_A.size()].size()) - 1-i >= 0){
				L = 1 << ((int)log2(arr[j+eval_A.size()].size()) - 1-i);
			}else{
				L = 0;
			}
			if(L >= 1){
				for(int k = 0; k < L; k++){
					arr[j+eval_A.size()][k] = arr[j+eval_A.size()][2*k] + rand*(arr[j+eval_A.size()][2*k+1]-arr[j+eval_A.size()][2*k]);
					eval_B[j][k] = eval_B[j][2*k] + rand*(eval_B[j][2*k+1]-eval_B[j][2*k]);						
				}
			}else{
				arr[j+eval_A.size()][0] = (F(1)-rand)*arr[j+eval_A.size()][0];
				eval_B[j][0] = (F(1)-rand)*eval_B[j][0];
			
			}
			
		}
	}
	for(int i = 0; i < arr.size(); i++){
		P.vr.push_back(arr[i][0]);	
	}
	F sum = F(0);
	for(int i = 0; i < a.size(); i++){
		sum += a[i]*evals[i];
	}
	if(sum != polynomials[0].eval(0) + polynomials[0].eval(1)){
		printf("Error in batch sumcheck\n");
		exit(-1);
	}
	P.randomness.push_back(r);
	P.q_poly = polynomials;
	return P;
}

proof prove_linear_code_batch( vector<vector<F>> &codewords, int n, double &vt, double &ps){
	vector<F> A(2*n,F(0)),B(2*n,F(0));
	vector<F> r1 = generate_randomness((int)log2(A.size()));
    vector<F> r2 = generate_randomness((int)(log2(codewords.size())));
	vector<F> beta,beta2;precompute_beta(r1,beta);precompute_beta(r2,beta2);
	int lvl = 0;
    evaluate_parity_matrix(A, beta, 0, n, 0,lvl);
    for(int i = 0; i < codewords.size(); i++){
		for(int j = 0; j < codewords[i].size(); j++){
			B[j] += codewords[i][j]*beta2[i];
		}
	}
	proof P = generate_2product_sumcheck_proof(A,B,r1[r1.size()-1],vt,ps);
	if(P.q_poly[0].eval(0) + P.q_poly[0].eval(1) != F(0)){
		printf("Error in codeword\n");
		//exit(-1);
	}
	P.randomness.push_back(r1);
	P.randomness.push_back(r2);
	return P;
}

proof prove_linear_code( vector<F> &codeword, int n, double &vt, double &ps){
    vector<F> A(codeword.size(),F(0));
	vector<F> r1 = generate_randomness((int)log2(A.size()));
    vector<F> beta;precompute_beta(r1,beta);
    int lvl = 0;
    evaluate_parity_matrix(A, beta, 0, n, 0,lvl);
    proof P = generate_2product_sumcheck_proof(A,codeword,r1[r1.size()-1],vt,ps);
	if(P.q_poly[0].eval(0) + P.q_poly[0].eval(1) != F(0)){
		printf("Error in codeword\n");
		//exit(-1);
	}
	P.randomness.push_back(r1);
	return P;
	/*
	int max_size= 0;
	vector<F> eval_A(transcript.x1.size(),F(0)),eval_B(transcript.x2.size(),F(0));
	
	for(int i = 0; i < transcript.x1.size(); i++){
        pad_vector(transcript.x1[i]);
        if(transcript.x1[i].size() > max_size){
			max_size = transcript.x1[i].size();
		}
		pad_vector(transcript.x2[i]);
		pad_vector(transcript.x2_inp[i]);
		
		if(transcript.x2[i].size() > max_size){
			max_size = transcript.x2[i].size();
		}
	}

    vector<F> r = generate_randomness((int)log2(transcript.x2[0].size()));
    vector<F> r1,r2;
	for(int i = 0; i < r.size()/2; i++){
		r1.push_back(r[i]);
	}
	for(int i = r.size()/2; i < r.size(); i++){
		r2.push_back(r[i]);
	}
	vector<F> beta1,beta2;
	precompute_beta(r1,beta1);
	precompute_beta(r2,beta2);
	
	
	int j1,j2;
	int beta_log = r1.size();
	for(int i = 0; i < transcript.x1.size(); i++){
		for(int j = 0; j < transcript.x1[i].size(); j++){
			j2 = j%beta1.size();
			j1 = j>>(beta_log);
			eval_A[i] += beta1[j2]*beta2[j1]*transcript.x1[i][j];
		}
	}
	for(int i = 0; i < transcript.x2.size(); i++){
		for(int j = 0; j < transcript.x2[i].size(); j++){
			j2 = j%beta1.size();
			j1 = j>>(beta_log);
			eval_B[i] += beta1[j2]*beta2[j1]*transcript.x2[i][j];
		}
	}
	vector<vector<F>> A_arr,B_arr; 
	evaluate_matrixes(A_arr,B_arr,beta1,beta2,n, 0);
	for(int i = 0; i < A_arr.size(); i++){
		pad_vector(A_arr[i]);
		pad_vector(B_arr[i]);
	}


	int L = arr.size();
	vector<vector<F>> V;
	V.push_back(arr);
	
	for(int i = 0; i < transcript.x1.size()-1; i++){ V.push_back(transcript.x1[i]);}
	for(int i = 0; i < transcript.x2_inp.size(); i++){ V.push_back(transcript.x2_inp[i]);}
	


	F zero = F(0);
	vector<F> evals = eval_A;evals.insert(evals.end(),eval_B.begin(),eval_B.end());
	
	// First sumcheck to prove all parital matrix-vecrtor multitplications
	proof P1 = batch_sumcheck(V,A_arr,B_arr,evals);
		
		
	// release unessesary memory
	for(int i = 0; i < A_arr.size(); i++){vector<F>().swap(A_arr[i]);}
	for(int i = 0; i < B_arr.size(); i++){vector<F>().swap(B_arr[i]);}
	vector<vector<F>>().swap(A_arr);
	vector<vector<F>>().swap(B_arr);
	
	// Reduce all claimed evalautions for each part of the codeword into one
	vector<F> _r = P1.randomness[0],_r1,_r2;
	for(int i = 0; i < _r.size()/2; i++){
		_r1.push_back(_r[i]);
	}
	for(int i = _r.size()/2; i < _r.size(); i++){
		_r2.push_back(_r[i]);
	}
	
	vector<F> _beta1,_beta2,_eval_A(eval_A.size(),F(0)),_eval_B(eval_B.size(),F(0));
	precompute_beta(_r1,_beta1);
	precompute_beta(_r2,_beta2);
	
	for(int i = 0; i < transcript.x1.size(); i++){_eval_A[i] = P1.vr[i]; }
	for(int i = 0; i < transcript.x2.size(); i++){_eval_B[i] = P1.vr[i +transcript.x1.size()];}
	
	vector<F> input1,input2;
	vector<F> a = generate_randomness(eval_B.size() + eval_A.size()+1);
	vector<F> b = generate_randomness(1);
	// Generate a unified sumcheck for the entire codeword
	vector<F> codeword(2*arr.size(),F(0));
	vector<F> betas(2*arr.size());
	F sum = F(0);
	for(int i = 0; i < arr.size(); i++){
		codeword[i] = arr[i];
	}
	for(int i = 0; i < arr.size(); i++){
		int _j1 = i%_beta1.size();
		int _j2 = i>>((int)log2(_beta1.size()));
		betas[i] = a[0]*b[0]*_beta1[_j1]*_beta2[_j2];
	}
	int counter =arr.size();
	for(int i = 0; i < transcript.x1.size(); i++){
		F tsum = F(0);
		for(int j = 0; j < transcript.x1[i].size(); j++){
			int j1 = j%beta1.size();
			int j2 = j>>(beta_log);
			int _j1 = j%_beta1.size();
			int _j2 = j>>((int)log2(_beta1.size()));
			if(i != transcript.x1.size()-1){
				betas[counter] = a[i+1]*(beta1[j1]*beta2[j2]+b[0]*_beta1[_j1]*_beta2[_j2]);
			}else{
				betas[counter] = a[i+1]*beta1[j1]*beta2[j2];
			}
			tsum += betas[counter]*transcript.x1[i][j];
			codeword[counter++] = transcript.x1[i][j];
		}
		
	}
	for(int i= 0; i < transcript.x2.size(); i++){
		F tsum = F(0);
		
		for(int j = 0; j < transcript.x2[i].size(); j++){
			int j1 = j%beta1.size();
			int j2 = j>>(beta_log);
			int _j1 = j%_beta1.size();
			int _j2 = j>>((int)log2(_beta1.size()));
			betas[counter] = a[i+1+transcript.x1.size()]*(beta1[j1]*beta2[j2]);
			//betas[counter] = a[i+1+transcript.x1.size()]*(beta1[j1]*beta2[j2]+b[0]*_beta1[_j1]*_beta2[_j2]);
			tsum += betas[counter]*transcript.x2[i][j];

			codeword[counter++] = transcript.x2[i][j];	
		}
		if(tsum != a[i+1+transcript.x1.size()]*(eval_B[i])){
			printf("Error %d\n",i);
		}
	}

	printf("%d,%d\n",codeword.size(),counter);
	sum += a[0]*b[0]*_eval_A[0];
	for(int i = 0; i < transcript.x1.size(); i++){
		if(i < transcript.x1.size()-1){
			sum += a[i+1]*(eval_A[i] + b[0]*_eval_A[i+1]);
		}else{
			sum += a[i+1]*eval_A[i];
		}
	}
	for(int i = 0; i < transcript.x2.size(); i++){
		sum +=  a[i+transcript.x1.size()+1]*(eval_B[i]);
	}

	proof P2 = generate_2product_sumcheck_proof(betas,codeword,F(323)); 
	if(sum != P2.q_poly[0].eval(0) + P2.q_poly[0].eval(1)){
		printf("Error in 2nd sumcheck\n");
		exit(-1);
	}
	encoding_proof P;
	P.P1 = P1;P.P2 = P2;	
	*/
	
	return P;
}

proof prove_membership(vector<F> &aggr_arr, vector<F> &encoded_arr, double &vt, double &ps){
	vector<F> in1,in2,in3;
	in1.insert(in1.begin(),aggr_arr.begin(),aggr_arr.end());
	in1.insert(in1.begin(),encoded_arr.begin(),encoded_arr.end());
	in2.resize(in1.size());
	vector<F> r = generate_randomness((int)log2(in1.size()));
	precompute_beta(r,in3);
	F one = 1;
	for(int i = 0; i < 3000; i++){
		in2[i] = one;
	}
	return _generate_3product_sumcheck_proof(in1,in2,in3,r[r.size()-1],vt,ps);
}


