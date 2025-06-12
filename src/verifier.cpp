#include "verifier.h"
#include "Kopis.h"


extern int recursion;
extern int MAX_CHUNCK;
double verification_time = 0.0;
int _proof_len = 0;


void verify_3product_sumcheck(proof P, vector<F> beta, F sum){
	clock_t t1,t2;
	F a;
	t1 = clock();
	_proof_len += sizeof(P.randomness[0][0])*(4*P.randomness[0].size() + 2);
	for(int i = 0; i < P.randomness[0].size(); i++){
		a = random();a = random();a = random();a = random();a = random();
		if(P.c_poly[i].eval(F_ZERO) + P.c_poly[i].eval(F_ONE) != sum){
			printf("Error in 3prod verification %d\n",i);
		}
		sum = P.c_poly[i].eval(P.randomness[0][i]);
	}
	F v3 = F(1);

	if(beta.size() != P.randomness[0].size() && beta.size() != 0){
		printf("Error in beta size verification\n");
		exit(-1);
	}
	for(int i = 0; i < beta.size(); i++){
		v3 *= ((beta[i]*P.randomness[0][i]) + ((F_ONE - beta[i])*(F_ONE-P.randomness[0][i])));
	}	
	t2 = clock();
	verification_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;


}

void verify_2product_sumcheck(proof P, F sum){
	clock_t t1,t2;
	t1 = clock();
	F a;
	_proof_len += sizeof(P.randomness[0][0])*(3*P.randomness[0].size() + 2);
	for(int i = 0; i < P.randomness[0].size(); i++){
		a = random();a = random();a = random();a = random();
		if(P.q_poly[i].eval(F_ZERO) + P.q_poly[i].eval(F_ONE) != sum){
			printf("Error in 2prod verification %d \n",i);
		}
		sum =  P.q_poly[i].eval(P.randomness[0][i]);
	}
	t2 = clock();
	verification_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
}

void sum_poly_extended(F sum, vector<F> poly, vector<F> poly_sum, int c){
	
	for(int i = (poly.size() - (1<<c)); i < poly.size(); i++){
        sum -= poly[i];
    }
    for(int i = 0; i < poly_sum.size(); i++){
        sum-=poly_sum[i];
    }
	if(sum != F(0)){
        printf("Verification Error \n");
        //exit(-1);
    }
}

void sum_poly(F sum, vector<F> poly, vector<F> poly_sum, int c){
	for(int i = 0; i < poly.size()/2; i++){
		sum -= poly[2*i];
	}
    for(int i = 0; i < poly_sum.size(); i++){
        sum -= poly_sum[i];
    }
	if(sum != 0){
		printf("Error in stream sum_poly\n");
	}

}

F evaluate_poly_extended(vector<F> poly, vector<F> poly_sum, F r, int c){
	vector<F> L = compute_lagrange_coeff(getRootOfUnity(c),r,1ULL<<(c));
	F sum = F(0);
	int idx = 0;
	
	for(int i = 0; i < 1<<c; i++){
		for(int j = i+1; j < 1<<c; j++){
			sum += L[i]*L[j]*poly[idx];
			idx++;
		}
	}
	for(int i = 0; i < 1<<c; i++){
		sum += L[i]*L[i]*poly[idx];
		sum += L[i]*poly_sum[i];
        idx++;
	}
	return sum;
}

F evaluate_poly(vector<F> poly, vector<F> poly_sum, F r, int c){
	int degree = (int)log2(poly.size());
	vector<F> L = compute_lagrange_coeff(getRootOfUnity(degree),r,1ULL<<(degree));
	vector<F> L2 = compute_lagrange_coeff(getRootOfUnity(degree-1),r,1ULL<<(degree-1));
	F sum = 0;
	for(int i = 0; i < L.size(); i++){
		sum += L[i]*poly[i];
	}
    for(int i = 0; i < L2.size(); i++){
        sum += L2[i]*poly_sum[i];
    }
	return sum;
}

void verify_linear_time_sumcheck(proof_stream P, F sum){
	vector<F> r;
	F K,K_sum;
	clock_t t1,t2;
	if(P.P.size() == 1){
		verify_2product_sumcheck( P.P[0], sum);
		return;
	}
	t1 = clock();
	K = P.transcript[0]; K_sum = P.transcript[1];
	F K_fold = K + K_sum;
	r.push_back(1);
	int counter= 2;
	for(int i = 1; i < P.size/MAX_CHUNCK; i++){
			F K1 = P.transcript[counter++];//.push_back(K);
			F K2 = P.transcript[counter++];//fold_transcript.push_back(K_sum);
			F K3 = P.transcript[counter++];//fold_transcript.push_back(K_P);
			K += K1;
			K_sum += K2;

			F a = K1;
			mimc_hash(a,K2);
			mimc_hash(a,K3);
			r.push_back(a);
			K_fold = (K_fold + a*a*K1 + a*(K3+K2));	
	}
	if(K + K_sum != sum){
		printf("Error in sumcheck\n");
		exit(-1);
	}
	t2 = clock();
	
	verification_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	_proof_len += sizeof(P.transcript[0])*(P.transcript.size());
	
	verify_2product_sumcheck( P.P[0], K_fold);
	verify_2product_sumcheck( P.P[1], P.P[1].q_poly[0].eval(0)+P.P[1].q_poly[0].eval(1));

}

void verify_stream_2product_sumcheck(proof_stream P, F sum){
	if(MAX_CHUNCK >= P.size){
		if(P.P[0].q_poly[0].eval(F_ZERO) +P.P[0].q_poly[0].eval(F_ONE) != sum){
            printf("Error in V\n");
            exit(-1);
        }
		verify_2product_sumcheck( P.P[0], sum);
	
		return;
	}
	clock_t t1,t2;
	t1 = clock();

	
	int total_c = (int)log2(P.size/MAX_CHUNCK);
    int c = 4;
	if(c >= total_c){
        c = total_c;
    }else{
		c = (int)log2(log2(P.size/MAX_CHUNCK)) + 1;
	}
	
	sum_poly_extended(sum,P.polynomials[0],P.polynomials[1],c);
	sum = evaluate_poly_extended(P.polynomials[0],P.polynomials[1],P.randomness[0],c);
	
	/****=========****/
	
	_proof_len += sizeof(P.polynomials[0][0])*(P.polynomials[0].size());
	
	
	/*******/
	
    int new_c = total_c -c;
	if(new_c != 0){
		if(new_c <= 4){
	
			sum_poly_extended(sum,P.polynomials[2],P.polynomials[3],new_c);
			sum = evaluate_poly_extended(P.polynomials[2],P.polynomials[3],P.randomness[1],new_c);
		}else{
			if(!recursion){
					_proof_len += sizeof(P.polynomials[2][0])*(P.polynomials[2].size());
					sum_poly(sum,P.polynomials[2],P.polynomials[3],new_c);
					sum = evaluate_poly(P.polynomials[2],P.polynomials[3],P.randomness[1],new_c);
		
				}else{
					
				}
			
		}
	}
	t2 = clock();
	verification_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;

	verify_2product_sumcheck( P.P[0], sum);
	sum = P._a[0]*P.P[0].vr[0] + P._a[1]*P.P[0].vr[1] + P._a[2]*P.P[0].vr[2];
	verify_2product_sumcheck( P.P[1], sum);




}