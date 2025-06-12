#include "PC_utils.h"
#include "parameter.h"
#include "Virgo.h"
extern bool linear_time;
extern int tensor_row_size;
shockwave_data *C_f;
shockwave_data *C_c;

void _compute_tensorcode(F *message, F **tensor, int N){
    for(int i = 0; i < 2*tensor_row_size; i++){
        for(int j = 0; j < 2*N/tensor_row_size; j++){
            tensor[i][j] = F(0);
        }
    }
    
    int counter = 0;
    for(int i = 0; i < tensor_row_size; i++){
        for(int j = 0; j < N/tensor_row_size; j++){
            tensor[i][j] = message[counter++];
        }
    }
    if(!linear_time){
        #pragma omp parallel for
        for(int i = 0; i < tensor_row_size; i++){        
            _fft(tensor[i],((int)log2(N/tensor_row_size))+1,false);
        }

        #pragma omp parallel for
        for(int i = 0; i < 2*N/tensor_row_size; i++){
            vector<F> buff(2*tensor_row_size,F(0));
            
            for(int j = 0; j < tensor_row_size; j++){
                buff[j] = tensor[j][i];
            }
            _fft(buff.data(),(int)log2(2*tensor_row_size),false);
            for(int j = 0; j < 2*tensor_row_size; j++){
                tensor[j][i] = buff[j];
            }
        }
    }else{
        
        #pragma omp parallel for
        for(int i = 0; i < tensor_row_size; i++){        
            _fft(tensor[i],(int)log2(2*N/tensor_row_size),false);
        }    
       
        #pragma omp parallel for
        for(int i = 0; i < 2*N/tensor_row_size; i++){
            vector<F> buff(tensor_row_size,F(0));
            for(int j = 0; j < tensor_row_size; j++){
                buff[j] = tensor[j][i];
            }
            vector<F> buff2(2*tensor_row_size,F(0));
            //encode_monolithic_alt(buff.data(), buff2.data(),buff.size(),_scratch);
            encode_monolithic(buff.data(),buff2.data(), buff.size());
            
            for(int j = 0; j < 2*tensor_row_size; j++){
                tensor[j][i] = buff2[j];
            }
        }
        
        
    }    
}

void compute_tensorcode(vector<F> &message, vector<vector<F>> &tensor){
    if(tensor.size() == 0){
        tensor.resize(2*tensor_row_size);
        for(int i = 0; i < 2*tensor_row_size; i++){
            tensor[i].resize(2*message.size()/tensor_row_size,F(0));
        }
    }else{
        for(int i = 0; i < tensor.size(); i++){
            for(int j = 0; j < tensor[i].size(); j++){
                tensor[i][j] = F(0);
            }
        }
    }
    int counter = 0;
    for(int i = 0; i < tensor_row_size; i++){
        for(int j = 0; j < message.size()/tensor_row_size; j++){
            tensor[i][j] = message[counter++];
        }
    }
    if(!linear_time){
        #pragma omp parallel for
        for(int i = 0; i < tensor_row_size; i++){        
            _fft(tensor[i].data(),((int)log2(message.size()/tensor_row_size))+1,false);
        }
        #pragma omp parallel for
        for(int i = 0; i < tensor[0].size(); i++){
            vector<F> buff(2*tensor_row_size,F(0));
            
            for(int j = 0; j < tensor_row_size; j++){
                buff[j] = tensor[j][i];
            }
            _fft(buff.data(),(int)log2(2*tensor_row_size),false);
            for(int j = 0; j < 2*tensor_row_size; j++){
                tensor[j][i] = buff[j];
            }
        }
    }else{
        
        #pragma omp parallel for
        for(int i = 0; i < tensor_row_size; i++){        
            _fft(tensor[i].data(),(int)log2(tensor[i].size()),false);
        }

        #pragma omp parallel for
        for(int i = 0; i < tensor[0].size(); i++){
            vector<F> buff(tensor_row_size,F(0));
            for(int j = 0; j < tensor_row_size; j++){
                buff[j] = tensor[j][i];
            }
            vector<F> buff2(2*tensor_row_size,F(0));
            encode_monolithic(buff.data(),buff2.data(), buff.size());
            //encode(buff.data(),buff2.data(),buff.size());
            for(int j = 0; j < 2*tensor_row_size; j++){
                tensor[j][i] = buff2[j];
            }
        }
    }    
}
bool _compareFirstElement(const std::vector<size_t> &a, const std::vector<size_t> &b) {
    return a[0] < b[0];
}
void _find_collumns(vector<vector<size_t>> &I, vector <size_t> &C, vector<vector<size_t>> &I_sorted){
    vector<int> I_t;
    I_sorted = I;
    for(int i = 0; i < I.size(); i++){
        I_t.push_back(I[i][0]);
    }
    std::sort(I_sorted.begin(), I_sorted.end(), _compareFirstElement);
    std::sort(I_t.begin(),I_t.end());
    C.push_back(I_t[0]);
    for(int i = 1; i < I_t.size(); i++){
        if(I_t[i] != I_t[i-1]){
            C.push_back(I_t[i]);
        }
    }
}

int _next_pow2(int l){
    if(l != 1ULL<<((int)log2(l))){
        return 1ULL<<((int)log2(l)+1);
    }
    return l;
}

void recursive_prover_orion(vector<vector<F>> &codewords, double &vt,double &ps){
    shockwave_data *C;
    printf("%d,%d\n",codewords.size(),codewords[0].size());
    vector<F> arr = convert2vector(codewords);
    pad_vector(arr);
    clock_t t1,t2;
    t1 = clock();
    C = shockwave_commit(arr,32);
    t2 = clock();
    printf("%lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC);
    commit_parity_matrix(codewords[0].size()/2);
    proof P1 = prove_linear_code_batch(codewords,codewords[0].size()/2,vt,ps);
    
    open_parity_matrix(P1.randomness[0], P1.randomness[1], codewords[0].size()/2, vt, ps);
    vector<F> r = P1.randomness[0];r.insert(r.end(),P1.randomness[2].begin(),P1.randomness[2].end());
    shockwave_prove(C,r,vt,ps);
}

void recursive_prover_Spielman_stream(vector<F> &input,vector<vector<F>> &M,vector<vector<F>> &codewords , vector<vector<size_t>> I,double &vt , double &ps){
    vector<F> buff1,buff2;
    int counter = 0;
    vector<vector<F>> Tc;

    
    std::unordered_map<size_t, vector<size_t>> column_map;
        vector<size_t> columns;

        for(int  i =0; i < I.size(); i++){
            columns.push_back(I[i][0]);
        }
        std::sort(columns.begin(), columns.end());
        auto it = std::unique(columns.begin(), columns.end());
        columns.erase(it, columns.end());
        for(int i = 0; i < I.size(); i++){
            column_map[I[i][0]].push_back(I[i][1]);
        }
        vector<int> remaining_columns;
        bool flag = false;
        for(int i = 0; i < columns.size(); i++){
            for(int j = 0; j < column_map[columns[i]].size(); j++){
                if(column_map[columns[i]][j] >= tensor_row_size){
                    flag = true;
                    break;
                }
            }
            if(flag){
                
                remaining_columns.push_back(columns[i]);
            }
            flag = false;
        }
    // receive random element s
    vector<F> s(codewords.size());
    s[0] = random();
    for(int i = 1; i < s.size(); i++){
        s[i] = s[i-1]*s[0];
    }
    vector<F> aggr_c(codewords[0].size(),F(0));
    for(int i = 0; i < codewords.size(); i++){
        for(int j = 0; j < codewords[i].size(); j++){
            aggr_c[j] += s[i]*codewords[i][j];
        }
    }
    clock_t t1,t2;
    proof P1 = prove_linear_code(aggr_c,aggr_c.size()/2,vt,ps );
    t1 = clock(); 
    precompute_beta(P1.randomness[0],buff1);
    vector<F> evals(M[0].size(),F(0));
    
    for(int i = 0; i < M[0].size(); i++){
        for(int j = 0; j < codewords[0].size()/2; j++){
            evals[i] += buff1[j]*M[j][i];
        }
    }
    vector<F> sM(M[0].size());
    for(int j = 0; j < remaining_columns.size(); j++){
        sM[remaining_columns[j]] = s[counter++];
    }
    t2 = clock();
    t1 = clock();
    proof P2 = generate_2product_sumcheck_proof(sM,evals,F(021),vt,ps );
    
    buff1 = convert2vector(codewords);
    pad_vector(buff1);
    buff2.clear();buff2.resize(buff1.size(),F(0));
    F s2 = random();
    for(int i = 0 ; i < I.size(); i++){
        buff2[i] = s2;
        s2 = s2*s2;
    }
    t1 = clock();
    proof P3 = generate_2product_sumcheck_proof(buff1,buff2,F(121),vt,ps );
    t2 = clock();
    
    vector<F> r = P3.randomness[0];
    t1 = clock();
    shockwave_prove(C_c,r,vt,ps);
    t2 = clock();
    buff1 = convert2vector(M);
    r = P1.randomness[0];P1.randomness[0].pop_back();
    r.insert(r.end(),P2.randomness[0].begin(),P2.randomness[0].end());
    F y1 = evaluate_vector(buff1,r);
    vector<vector<F>> initial_tensor(M.size());
    counter = 0;
    for(int i = 0; i < initial_tensor.size(); i++){
        initial_tensor[i].resize(M[i].size()/(2));
        for(int j = 0; j < initial_tensor[i].size(); j++){
            initial_tensor[i][j] = input[counter++];
        }
    }
    t1 = clock();
    proof P5 = prove_fft_matrix(initial_tensor,r,y1,vt,ps );
    t2 = clock();   
    P5.randomness[0].pop_back();
    //printf(">> %d,%d\n",C_f->N,P5.randomness[0].size());
    t1 = clock();
    shockwave_prove(C_f,P5.randomness[0],vt,ps);
    t2 = clock();
}


void recursive_prover_Spielman(vector<F> &input,vector<vector<F>> &C, vector<size_t> I,double &vt , double &ps){
    vector<F> buff1,buff2;
    vector<vector<F>> M_prime(C.size());
    int counter = 0;
    vector<vector<F>> Tc;
    //compute_tensorcode(input,Tc);
    for(int i = 0; i < M_prime.size(); i++){
        M_prime[i].resize(C[i].size(),F(0));
        for(int j = 0; j < C[i].size()/2; j++){
            M_prime[i][j] = input[counter++];
        }
        _fft(M_prime[i].data(),(int)log2(M_prime[i].size()),false);
        //for(int j = 0; j < C[i].size(); j++){
            //if(Tc[i][j] != M_prime[i][j]){
            //    printf("ERrror %d,%d\n",i,j);
            //    exit(-1);
            //}
        //}
    }    
    

    // receive random element s
    vector<F> s(M_prime[0].size());
    s[0] = random();
    for(int i = 1; i < s.size(); i++){
        s[i] = s[i-1]*s[0];
    }
    vector<F> aggr_c(2*M_prime.size(),F(0));
    for(int i = 0; i < M_prime.size(); i++){
        for(int j = 0; j < M_prime[i].size(); j++){
            aggr_c[i] += s[j]*M_prime[i][j];
        }
    }

    for(int i = 0; i < C.size(); i++){
        for(int j = 0; j < C[i].size(); j++){
            aggr_c[i+ M_prime.size()] += s[j]*C[i][j];
        }
    }
    proof P1 = prove_linear_code(aggr_c,M_prime.size(),vt,ps );
    precompute_beta(P1.randomness[0],buff1);
    vector<F> evals(M_prime[0].size(),F(0));
    for(int i = 0; i < M_prime[0].size(); i++){
        for(int j = 0; j <  M_prime.size(); j++){
            evals[i] += buff1[j]*M_prime[j][i];
        }
        for(int j = 0; j  < C.size(); j++){
            evals[i] += buff1[j+M_prime.size()]*C[j][i];
        }
    }
    
    proof P2 = generate_2product_sumcheck_proof(s,evals,F(021),vt,ps );
    if(P2.q_poly[0].eval(0)+P2.q_poly[0].eval(1) != P1.vr[1]){
        printf("Error recursion 1\n");
        exit(-1);
    }
    buff1 = convert2vector(M_prime);
    buff2 = convert2vector(C);
    buff1.insert(buff1.end(),buff2.begin(),buff2.end());
    buff2.clear();buff2.resize(buff1.size(),F(0));
    F s2 = random();
    buff2[I[0]] = s2;
    for(int i = 1; i < I.size(); i++){
        buff2[I[i]] = buff2[I[i-1]]*s2;
    }
    
    
    proof P3 = generate_2product_sumcheck_proof(buff1,buff2,F(121),vt,ps );
    
    F a = random();
    vector<F> r = P2.randomness[0];
    r.insert(r.end(),P1.randomness[0].begin(),P1.randomness[0].end());
    buff1.clear();precompute_beta(r,buff1);
    buff2.clear();precompute_beta(P3.randomness[0],buff2);
    for(int i = 0; i < buff1.size(); i++){
        buff1[i] += a*buff2[i];    
    }
    buff2.clear();buff2.resize(M_prime.size()*M_prime[0].size()*2,F(0));
    counter = 0;
    for(int i = 0; i < M_prime.size(); i++){
        for(int j = 0; j < M_prime[i].size(); j++){
            buff2[counter++] = M_prime[i][j];
        }
    }
    for(int i = 0; i < C.size(); i++){
        for(int j = 0; j < C[i].size(); j++){
            buff2[counter++] = C[i][j];
        }
    }
    proof P4 = generate_2product_sumcheck_proof(buff1,buff2,F(312),vt,ps );
    
    if(P4.q_poly[0].eval(F(0)) + P4.q_poly[0].eval(F(1)) != a*P3.vr[0] + P2.vr[1]){
        printf("Error recursion 2\n");
        exit(-1);
    }
    r = P4.randomness[0];r.pop_back();
    
    shockwave_prove(C_c,r,vt,ps);
    
    buff1 = convert2vector(M_prime);
    F y1 = evaluate_vector(buff1,r);

    vector<vector<F>> initial_tensor(M_prime.size());
    counter = 0;
    for(int i = 0; i < initial_tensor.size(); i++){
        initial_tensor[i].resize(M_prime[i].size()/(2));
        for(int j = 0; j < initial_tensor[i].size(); j++){
            initial_tensor[i][j] = input[counter++];
        }
    }
    proof P5 = prove_fft_matrix(initial_tensor,r,y1,vt,ps );
    
    P5.randomness[0].pop_back();
    //printf(">> %d,%d\n",C_f->N,P5.randomness[0].size());
    shockwave_prove(C_f,P5.randomness[0],vt,ps);
    
}

void recursive_prover_brakingbase(vector<F> &codeword, vector<size_t> I, double &vt, double &ps){
    commit_parity_matrix(codeword.size()/2);
    proof P1 = prove_linear_code(codeword,codeword.size()/2,vt,ps);
    open_parity_matrix(P1.randomness[0], P1.randomness[1], codeword.size()/2, vt, ps);
    shockwave_prove(C_c,P1.randomness[0],vt,ps);
}

void recursive_prover_RS(vector<F> &aggregated_vector, vector<vector<size_t>> I,double &vt, double &ps ){
    vector<vector<F>> aggregated_matrix(tensor_row_size);
    vector<vector<F>> out_1(tensor_row_size);
    vector<vector<F>> out_2(tensor_row_size);

    vector<size_t> collumns;
    vector<vector<size_t>> I_sorted;
    _find_collumns(I, collumns,I_sorted);
    vector<vector<F>> selected_collumns(_next_pow2(collumns.size()));
    for(int i = 0; i < tensor_row_size; i++){
        aggregated_matrix[i].resize(aggregated_vector.size()/tensor_row_size);
        out_1[i].resize(2*aggregated_vector.size()/tensor_row_size,F(0));
        //out_2[i].resize(2*aggregated_vector.size()/tensor_row_size,F(0));
        for(int j = 0; j < aggregated_vector.size()/tensor_row_size; j++){
            aggregated_matrix[i][j] = aggregated_vector[i*aggregated_vector.size()/tensor_row_size+j];
            out_1[i][j] = aggregated_matrix[i][j];
        }

    }
    
    for(int i = 0; i < tensor_row_size; i++){
        _fft(out_1[i].data(),(int)log2(out_1[i].size()),false);
    }
    
    for(int i = 0; i < selected_collumns.size(); i++){
        selected_collumns[i].resize(tensor_row_size,F(0));
        if(i < collumns.size()){
            for(int j = 0; j < tensor_row_size; j++){
                selected_collumns[i][j] = out_1[j][collumns[i]];
            }
        }
        
    }

    
    vector<vector<F>> out_3(_next_pow2(collumns.size()));
    //vector<vector<F>> out_4(next_pow2(collumns.size()));

    for(int i = 0; i < out_3.size(); i++){
        out_3[i].resize(2*tensor_row_size,F(0));
            for(int j = 0; j < out_3[i].size()/2; j++){
               out_3[i][j] = selected_collumns[i][j];
            }
        
        
        //out_4[i].resize(2*tensor_row_size,F(0));
    }
    

    for(int i = 0; i< collumns.size(); i++){
        _fft(out_3[i].data(),(int)log2(out_3[i].size()),false);
        //for(int j = 0; j < out_3[i].size(); j++){
        //    out_4[i][j] = out_3[i][j];
        //}
        //fft(out_4[i],(int)log2(out_4[i].size()),false);
    }

    
     auto s = std::chrono::steady_clock::now();

    vector<F> beta(collumns.size()*out_3[0].size(),F(0));
    
    vector<F> r = generate_randomness(I.size());
    
    int counter = 0;
    for(int i = 0; i < I.size(); i++){
        if(collumns[counter] != I_sorted[i][0]){
            counter++;
        }
        if(counter*(2*tensor_row_size) + I[i][1] >= collumns.size()*out_3[0].size()){
            printf("Error %d,%d,%d,%d\n",counter,collumns.size(), I[i][1],2*tensor_row_size);
        }
        beta[counter*(2*tensor_row_size) + I[i][1]] += r[i];
    }
    vector<F> v = convert2vector(out_3);
    pad_vector(v);pad_vector(beta);
    
    proof P0 = generate_2product_sumcheck_proof(v,beta,F(323),vt,ps );    
    
    
    //proof P1 = prove_fft_matrix(out_3, P0.randomness[0], P0.vr[0]);
    //Elastic_PC_ps += (double)P1.q_poly.size()*3*sizeof(F(1))/(1024.0);
    
    proof P2 = prove_fft_matrix((selected_collumns), P0.randomness[0], P0.vr[0],vt,ps );
    
    vector<F> r_point;
    for(int i = (int)log2(tensor_row_size); i < P2.randomness[0].size(); i++){
        r_point.push_back(P2.randomness[0][i]);
    }
    
    r.clear();
    precompute_beta(r_point,r);
    beta.clear(); beta.resize(out_1.size()*out_1[0].size(),F(0));
    
    
    for(int i = 0; i < collumns.size(); i++){
        for(int j = 0; j < tensor_row_size; j++){
            beta[collumns[i] + j*2*aggregated_vector.size()/tensor_row_size] = r[i];
        }
    }
    v = convert2vector(out_1);
    proof P3 = generate_2product_sumcheck_proof(v,beta,F(323),vt,ps );
    
    
    //proof P4 = prove_fft_matrix(out_1, P3.randomness[0], P3.vr[0]);
    //Elastic_PC_ps += (double)P4.q_poly.size()*3*sizeof(F(1))/(1024.0);
    proof P5 = prove_fft_matrix(aggregated_matrix, P3.randomness[0], P3.vr[0],vt,ps );
    
    vector<F> r_x = P5.randomness[0];
 
    shockwave_prove(C_f,r_x,vt,ps);
    //virgo_open(aggregated_vector,r_x,virgo_Commitment,Elastic_PC_vt,Elastic_PC_ps);
    auto e = std::chrono::steady_clock::now();

    //printf("%lf \n", std::chrono::duration_cast<std::chrono::duration<double>>(e - s).count());
    
}
