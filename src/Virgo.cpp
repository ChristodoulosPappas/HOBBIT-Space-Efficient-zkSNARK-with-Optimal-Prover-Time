
#include "Virgo.h"
#include "polynomial.h"
#include "sumcheck.h"
// We can save space by not storing all data
void MT_commit(vector<F> &elements, vector<vector<__hhash_digest>> &hashes, int partitions){
    if(partitions == 1){
        vector<__hhash_digest> buff(elements.size()/4);
        hashes.resize((int)log2(elements.size()/4) +1);
        for(int i = 0; i < buff.size(); i++){
            memset(&buff[i], 0, sizeof(__hhash_digest));
        }
        for(int j = 0; j < elements.size()/4; j+=1){    
            buff[j] = merkle_tree::hash_double_field_element_merkle_damgard(elements[4*j], elements[4*j+1],elements[4*j+2],elements[4*j+3], buff[j]);
        }
        hashes[0] = (buff);
        merkle_tree::merkle_tree_prover::create_tree( buff.size() , hashes, sizeof(__hhash_digest), true);
    }else{
        vector<__hhash_digest> buff(elements.size()/(partitions));
        hashes.resize((int)log2(elements.size()/(partitions)) +1);
        for(int i = 0; i < buff.size(); i++){
            memset(&buff[i], 0, sizeof(__hhash_digest));
        }
        for(int j = 0; j < elements.size()/partitions; j+=1){    
            for(int k = 0; k < partitions/4; k++){
                buff[j] = merkle_tree::hash_double_field_element_merkle_damgard(elements[j*partitions + 4*k], elements[j*partitions + 4*k+1],elements[j*partitions + 4*k+2],elements[j*partitions + 4*k+3], buff[j]);
            }
        }
        hashes[0] = (buff);
        merkle_tree::merkle_tree_prover::create_tree( buff.size() , hashes, sizeof(__hhash_digest), true);
    }
    
}

MT_proof MT_Open(size_t idx, vector<vector<__hhash_digest>> &hashes){
    MT_proof P;
    P.idx = idx;
    for(int i = 0; i < hashes.size(); i++){
        if(idx%2 == 0){
            P.path.push_back(hashes[i][idx+1]);
        }else{
            P.path.push_back(hashes[i][idx-1]);
        }

        idx = idx/2;
    }
    return P;
}

void MT_verify(MT_proof P, vector<F> elements, size_t idx){
    __hhash_digest H;
    memset(&H, 0, sizeof(__hhash_digest));
    if(elements.size() % 4 == 0){
        for(int i = 0; i < elements.size()/4; i++){
            H = merkle_tree::hash_double_field_element_merkle_damgard(elements[4*i], elements[4*i+1],elements[4*i+2],elements[4*i+3], H);
        }    
    }else{
        for(int i = 0; i < (elements.size() - (elements.size() % 4))/4; i++){
            H = merkle_tree::hash_double_field_element_merkle_damgard(elements[4*i], elements[4*i+1],elements[4*i+2],elements[4*i+3], H);
        }
        for(int i = (elements.size() - (elements.size() % 4)); i < elements.size(); i++){
            H = merkle_tree::hash_double_field_element_merkle_damgard(elements[4*i], F(0),F(0),F(0), H);
        }
    }
    __hhash_digest data[2];
   for(int i = 0; i < P.path.size(); i++){
        if(idx%2 == 0){
            data[0] = H;
            data[1] = P.path[i];
            my_hhash(data, &H);
        }else{
            data[1] = H;
            data[0] = P.path[i];
            my_hhash(data, &H);
        }
        idx = idx/2;
    } 
}
void Virgo_commit(vector<F> &poly, vector<F> &encoded_poly, vector<vector<__hhash_digest>> &hash_tree,int partitions){

}

F fold(int idx, vector<F> arr,vector<F> a, int N, int k){
    vector<F> omega_base(k);
    vector<F> omega(k);
    F two_inv = F(2).inv();
    for(int i  = 0 ; i < omega_base.size(); i++){
        F _omega = getRootOfUnity((int)log2(N/(1ULL<<(i)))).inv();
        omega_base[i] = _omega.fastPow(_omega,N/(1ULL<<(k-i)));
        _omega = getRootOfUnity((int)log2(N/(1ULL<<(i)))).inv();
        omega[i] = _omega.fastPow(_omega,idx);
        
    }
    for(int i = 0; i < k; i++){
        F div = omega[i];
        for(int j = 0; j < arr.size()/(1ULL<<(i+1)); j++){
            arr[j] = two_inv*(arr[2*j] + arr[2*j+1]) + div*two_inv*a[i]*(arr[2*j] - arr[2*j+1]);
            div = div*omega_base[i];
        }
    }
    return arr[0];
}

void change_form(vector<F> &poly, int logn, int l,int pos){
    vector<F> buff(1ULL<<(logn-l));
    for(int i = 0; i <  buff.size()/2; i++){
        buff[i] = poly[pos  + 2*i];
        buff[i + buff.size()/2] = poly[pos + 2*i+1]-poly[pos  + 2*i];
    }
    for(int i = pos; i < pos+buff.size(); i++){
        poly[i] = buff[i-pos];
    }
    if(l+1 == logn){
        return;
    }
    change_form(poly,logn,l+1,pos);
    change_form(poly,logn,l+1,pos+(buff.size()/2));    
}

shockwave_data* shockwave_commit(vector<F> &poly, int k){
    shockwave_data* data = new shockwave_data;

    data->k = k;
    data->N = poly.size();
    init_matrix(data->encoded_matrix,k,2*data->N/k);
    init_matrix(data->matrix,k,data->N/k);
    
    int counter = 0;
    for(int i = 0; i < k; i++){
        bool flag = false;
        for(int j = 0; j < data->N/k; j++){
            data->matrix[i][j] = poly[counter];
            if(poly[counter] != F(0)){
                flag = true;
            }
            data->encoded_matrix[i][j] = poly[counter++];
        }
        if(flag){
            _fft(data->encoded_matrix[i],(int)log2(2*data->N/k),false);
        }
    }
    vector<vector<_hash>> H;
    F *buff = new F[k];
    data->MT.resize((int)log2(2*data->N/k)+1);
    data->MT[0].resize(2*data->N/k);
    for(int i = 0; i < 2*data->N/k; i++){
        for(int j = 0; j < k; j++){
            buff[j] = data->encoded_matrix[j][i];
        }
        merkle_tree::merkle_tree_prover::MT_commit_Blake(buff,H,k);
        data->MT[0][i] = H[H.size()-1][0];
        H.clear();
    }
    delete[] buff;
    merkle_tree::merkle_tree_prover::create_tree_blake(data->MT[0].size(),data->MT,sizeof(__hhash_digest), true);
    return data;
}


void whir_commit(vector<F> &poly, Whir_data &data){
    data.k = 4;
    data.poly = poly;
    data.poly_com = poly;
    change_form(data.poly_com,(int)log2(data.poly_com.size()),0,0);
    data.poly_com.resize(data.poly_com.size()*2,F(0));
    _fft(data.poly_com.data(),(int)log2(data.poly_com.size()),false);
    F *buff = new F[data.poly_com.size()];
    int counter = 0;
    for(int j = 0; j < data.poly_com.size()/(1ULL<<data.k); j++){
        for(int k = 0; k < 1ULL<<data.k; k++){
            buff[counter++] = data.poly_com[j+k*data.poly_com.size()/(1ULL<<data.k)];
        }
    }
    for(int j = 0 ; j < data.poly_com.size(); j++){
        data.poly_com[j] = buff[j];
    }
    merkle_tree::merkle_tree_prover::MT_commit_Blake(data.poly_com.data(),data.MT,data.poly_com.size());
}

void FRI_commit(vector<F> &poly, PC_data &data){
    data.k = 4;
    data.poly = poly;
    data.poly_com.resize(16);
    data.MT.resize(16);
    F *buff = new F[poly.size()/16];
        
    for(int i = 0; i < 16; i++){
        data.poly_com[i].resize(poly.size()/16);
        for(int j = 0; j < data.poly_com[i].size(); j++){
            data.poly_com[i][j] = poly[i*data.poly_com[i].size() + j];
        }
        change_form(data.poly_com[i],(int)log2(data.poly_com[i].size()),0,0);
        data.poly_com[i].resize(2*data.poly_com[i].size(),F(0));
        fft(data.poly_com[i],(int)log2(data.poly_com[i].size()),false);
        int counter = 0;
        for(int j = 0; j < data.poly_com.size()/(1ULL<<data.k); j++){
            for(int k = 0; k < 1ULL<<data.k; k++){
                buff[counter++] = data.poly_com[i][j+k*data.poly_com.size()/(1ULL<<data.k)];
            }
        }
        for(int j = 0 ; j < data.poly_com[i].size(); j++){
            data.poly_com[i][j] = buff[j];
        }
        //merkle_tree::merkle_tree_prover::MT_commit(buff,data.MT[i],data.poly_com[i].size());    
    }
    delete[] buff;
    vector<vector<__hhash_digest>> H;
    buff = new F[16];
    data.MT.resize((int)log2(data.poly_com[0].size())+1);
    data.MT[0].resize(data.poly_com[0].size());
    for(int i = 0; i < data.poly_com[0].size(); i++){
        for(int j = 0; j < 16; j++){
            buff[j] = data.poly_com[j][i];
        }
        merkle_tree::merkle_tree_prover::MT_commit(buff,H,16);
        data.MT[0][i] = H[H.size()-1][0];
    }
    merkle_tree::merkle_tree_prover::create_tree(data.MT[0].size(),data.MT,sizeof(__hhash_digest), true);
}

void compute_zetas(vector<vector<F>> &zetas,vector<int> &z,int v, int N){
    //printf("%d\n",N);
    for(int i  = 0; i < zetas.size(); i++){
        zetas[i].resize(v);
    }
    zetas[0][0] = random();
    F omega = getRootOfUnity((int)log2(N));
    for(int i = 1 ; i < zetas.size(); i++){
        z.push_back(rand()%N);
        zetas[i][0] = omega.fastPow(omega,z[i-1]);
    }
    for(int i = 0; i < zetas.size(); i++){
        for(int j = 1; j < zetas[0].size(); j++){
            zetas[i][j] = zetas[i][j-1]*zetas[i][j-1];
        }
    }
}

void compute_betas(vector<vector<F>> &betas, vector<vector<F>> &zetas){
    for(int i = 0; i < zetas.size(); i++){
        precompute_beta(zetas[i],betas[i]);
    }
}

void _verify_iteration(Whir_data &data,vector<F> a, vector<int> r, int repeats,int iter, double &ps,double &vt){
        int k = data.k;
        int N = data.poly.size();
        clock_t start,end;
        
        
        vector<vector<F>> reply(r.size());
        for(int i = 0; i < r.size(); i++){
            for(int j = 0; j < 1ULL<<k; j++){
                if(iter == 1){
                    reply[i].push_back(data.poly_com[r[i]+j*data.poly_com.size()/(1ULL<<k)]);
                }else{
                    reply[i].push_back(data.FRI_poly[iter-2][r[i]+j*data.FRI_poly[iter-2].size()/(1ULL<<k)]);
                }
            }
        }
        // Verifiers steps
        ps += (1ULL<<k)*r.size()*sizeof(F)/1024.0;
        vector<vector<_hash>> paths(r.size());
        vector<size_t> pos(2);
        for(int i = 0; i < r.size(); i++){
            pos[0] = r[i];
            if(iter == 1){
                paths[i] = merkle_tree::merkle_tree_prover::open_tree_blake(data.MT,pos,0);
            }else{
                paths[i] = merkle_tree::merkle_tree_prover::open_tree_blake(data.FRI_MT[iter-2],pos,0);
            }
        }
        start = clock();
        int len;
        if(iter == 1){
            len = data.MT[0].size()*2;
        }else{
            len = data.FRI_MT[iter-2][0].size()*2;
        }
        bool *visited = new bool[2*len];
        for(int i = 0; i < 2*len; i++){
            visited[i] = false;
        }
        for(int i = 0; i < r.size(); i++){
            if(iter == 1){
                merkle_tree::merkle_tree_verifier::verify_claim_opt_blake(data.MT,paths[i].data(),r[i],data.MT[0].size(),visited,ps);
            }else{
                //printf("%d,%d\n",r[i],)
                merkle_tree::merkle_tree_verifier::verify_claim_opt_blake(data.FRI_MT[iter-2],paths[i].data(),r[i],data.FRI_MT[iter-2][0].size(),visited,ps);
            }
        }
       
        for(int i = 0; i < reply.size(); i++){
            if(iter == 1){
                fold(r[i],reply[i],a,data.MT[0].size(),k);
            }else{
                fold(r[i],reply[i],a,data.FRI_MT[iter-2][0].size(),k);
            }

        }
       
        
        end = clock();
        
        vt += (double)(end-start)/(double)CLOCKS_PER_SEC;
        delete[] visited;
}

void verify_iteration(PC_data &data,vector<F> a, vector<int> r, int repeats,int iter, double &ps,double &vt){
        int k = data.k;
        int N = data.poly.size();
        clock_t start,end;
        
        
        vector<vector<F>> reply(r.size());
        for(int i = 0; i < r.size(); i++){
            for(int j = 0; j < 1ULL<<k; j++){
                if(iter == 1){
                    reply[i].push_back(data.aggr_poly_com[r[i]+j*data.aggr_poly_com.size()/(1ULL<<k)]);
                }else{
                    reply[i].push_back(data.FRI_poly[iter-2][r[i]+j*data.FRI_poly[iter-2].size()/(1ULL<<k)]);
                }
            }
        }
        // Verifiers steps
        ps += (1ULL<<k)*r.size()*sizeof(F)/1024.0;
        vector<vector<__hhash_digest>> paths(r.size());
        vector<size_t> pos(2);
        for(int i = 0; i < r.size(); i++){
            pos[0] = r[i];
            if(iter == 1){
                paths[i] = merkle_tree::merkle_tree_prover::open_tree(data.aggr_MT,pos,0);
            }else{
                paths[i] = merkle_tree::merkle_tree_prover::open_tree(data.FRI_MT[iter-2],pos,0);
            }
        }
        start = clock();
        int len;
        if(iter == 1){
            len = data.MT[0].size()*2;
        }else{
            len = data.FRI_MT[iter-2][0].size()*2;
        }
        bool *visited = new bool[2*len];
        for(int i = 0; i < 2*len; i++){
            visited[i] = false;
        }
        for(int i = 0; i < r.size(); i++){
            if(iter == 1){
                merkle_tree::merkle_tree_verifier::verify_claim_opt(data.aggr_MT,paths[i].data(),r[i],data.aggr_MT[0].size(),visited,ps);
            }else{
                //printf("%d,%d\n",r[i],)
                merkle_tree::merkle_tree_verifier::verify_claim_opt(data.FRI_MT[iter-2],paths[i].data(),r[i],data.FRI_MT[iter-2][0].size(),visited,ps);
            }
        }
       
        for(int i = 0; i < reply.size(); i++){
            if(iter == 1){
                fold(r[i],reply[i],a,data.MT[0].size(),k);
            }else{
                fold(r[i],reply[i],a,data.FRI_MT[iter-2][0].size(),k);
            }

        }
       
        
        end = clock();
        
        vt += (double)(end-start)/(double)CLOCKS_PER_SEC;
        delete[] visited;
}

void aggregate(PC_data &data, vector<F> x, double &ps, double &vt){
    vector<F> temp_x;
    vector<F> temp_beta;
    for(int i  =0; i < 4; i++){
        temp_x.push_back(x[x.size()-4 + i]);
    }
    precompute_beta(temp_x,temp_beta);
    data.aggr_poly.resize(data.poly.size()/16,F(0));
    data.aggr_poly_com.resize(data.poly_com[0].size(),F(0));
    
    for(int i = 0; i < 16; i++){
        for(int j = 0; j < data.aggr_poly.size(); j++){
            data.aggr_poly[j] += data.poly[i*data.aggr_poly.size() + j]*temp_beta[i];
        }
    }
    
    for(int i = 0; i < data.aggr_poly_com.size(); i++){
        for(int j = 0; j < temp_beta.size(); j++){
            data.aggr_poly_com[i] += data.poly_com[j][i]*temp_beta[j];            
        }
    }
    
    merkle_tree::merkle_tree_prover::MT_commit(data.aggr_poly_com.data(),data.aggr_MT,data.aggr_poly_com.size());    
    
    
    vector<int> idx(240);
    for(int i = 0; i < 240; i++){
        idx[i] = rand()%(data.aggr_poly_com.size());
    }
    vector<vector<F>> reply(240);
    for(int i = 0; i < 240; i++){
        for(int j = 0; j < 16; j++){
            reply[i].push_back(data.poly_com[j][idx[i]]);
        }
    }
   
    
    ps += reply[0].size()*240*sizeof(F)/1024.0;
    vector<vector<__hhash_digest>> paths(240),H;
    bool *visited = new bool[2*data.MT[0].size()];
    for(int i = 0; i < 2*data.MT[0].size(); i++){
        visited[i] = false;
    }
    vector<size_t> pos(2);
    for(int i =0 ; i < 240; i++){
        pos[0] = idx[i];
        paths[i] = merkle_tree::merkle_tree_prover::open_tree(data.MT,pos,0);
    }
    clock_t t1,t2;
    t1 = clock();
    // THis must go in the first iteration  verification
    for(int i = 0; i < 240; i++){
        merkle_tree::merkle_tree_prover::MT_commit(reply[i].data(),H,reply[i].size());
    }
    for(int i = 0; i < 240; i++){
        merkle_tree::merkle_tree_verifier::verify_claim_opt(data.MT,paths[i].data(),idx[i],data.MT[0].size(),visited,ps);
    }
    t2 = clock();
    vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
    delete[] visited;
}

void shockwave_prove(shockwave_data *data, vector<F> x, double &vt, double &ps){
    
    vector<F> r1,beta1;
    int query_points = 240;
    for(int i = x.size()-(int)log2(data->k); i < x.size(); i++){
        r1.push_back(x[i]);
    }
    precompute_beta(r1,beta1);
    vector<F> aggr(data->N/data->k,F(0));
    vector<F> aggr_tensor(2*data->N/data->k,F(0));
    
    for(int i = 0; i < aggr_tensor.size(); i++){
        if(i < aggr.size()){
            for(int j = 0; j  < data->k; j++){
               aggr[i] += beta1[j]*data->matrix[j][i];
            }
        }
        for(int j = 0; j < data->k; j++){
            aggr_tensor[i] += beta1[j]*data->encoded_matrix[j][i];
        }
    }
    
    Whir_data C;
    if(aggr.size() > 1ULL<<8){
       whir_commit(aggr,C);
    }
    
    vector<int> I;
    vector<vector<F>> reply(query_points);
    for(int i = 0; i < query_points; i++){
        I.push_back(rand()%(2*aggr.size()));
    }
    for(int i = 0; i < reply.size(); i++){
        for(int j = 0; j < data->k; j++){
            reply[i].push_back(data->encoded_matrix[j][I[i]]);
        }
    }
    vector<F> buff1(aggr_tensor.size(),F(0));
    for(int i = 0; i  < I.size(); i++){
        buff1[I[i]] = F(1);
    }
    proof P1 = generate_2product_sumcheck_proof(aggr_tensor,buff1,F(33),vt,ps);
    proof P2 = prove_fft(aggr,P1.randomness[0],P1.vr[0],vt,ps);
    
    if(aggr.size()/2 > 1ULL<<8){
        _whir_prove(C,P2.randomness[0],vt,ps);
    }else{
        ps += aggr.size()*sizeof(F)/1024.0;
    }
    
    ps += (reply.size()*reply[0].size()*sizeof(F)/1024.0);
    clock_t s,e;
    s = clock();
    if(aggr.size()/2 <= 1ULL<<8){
        evaluate_vector(aggr,P2.randomness[0]);
    }
    vector<vector<_hash>> hashes;
    vector<F> o(query_points,F(0));
    vector<size_t> pos(2);pos[1] = 0;
    bool *visited = new bool[2*data->MT[0].size()];
    for(int i = 0; i < 2*data->MT[0].size(); i++){
        visited[i] = false;
    }
    for(int i = 0; i < reply.size(); i++){
        for(int j = 0; j < reply[i].size(); j++){
            o[i] += beta1[j]*reply[i][j];
        }
        merkle_tree::merkle_tree_prover::MT_commit_Blake(reply[i].data(),hashes,reply[i].size());
        hashes.clear();
        pos[0] = I[i];
        vector<_hash> path =  merkle_tree::merkle_tree_prover::open_tree_blake(data->MT,pos,0); 
        merkle_tree::merkle_tree_verifier::verify_claim_opt_blake(data->MT,path.data(),I[i],data->MT[0].size(),visited,ps);
    }
    e = clock();
    vt += (double)(e-s)/(double)CLOCKS_PER_SEC;
    delete[] visited;
    
    
    //free_matrix(data->matrix,data->k);   
    //free_matrix(data->encoded_matrix,data->k);   
    delete data;
        
}

void _whir_prove(Whir_data &data, vector<F> x, double &vt, double &ps){
    
    
    
    int k = 4;
    int N = data.poly.size();
   
    int iter = 0;
    clock_t start,end;
    data.FRI_poly.resize((int)log2(N)/k);
    data.FRI_MT.resize((int)log2(N)/k);
    
    vector<F> beta;
    vector<F> new_x;
    precompute_beta(x,beta);
    F eval = F(0);
    for(int i = 0; i < data.poly.size(); i++){
        eval += beta[i]*data.poly[i];
    }
    vector<F> a;
    //printf("Ratio : %d\n",data.poly_com.size()/data.poly.size());
    vector<vector<vector<F>>> zetas;
    vector<F> pows;
    vector<F> challenge;
    int remaining_size;
    int repeats = 100; //100-bit of security
    while(true){
        for(int i = 0; i < k; i++){
            quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
            quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		    linear_poly l1,l2;
            int L = N/(1ULL<<(iter*k + (i+1)));
            for(int j = 0; j < L; j++){
                l1 = linear_poly(data.poly[j+L] - data.poly[j],data.poly[j]);
                l2 = linear_poly(beta[j+L] - beta[j],beta[j]);
                temp_poly = l1*l2;
                poly = poly + temp_poly;
            }
            ps+= (3*sizeof(F))/1024.0;
            start = clock();
            a.push_back(random());
            if(poly.eval(0)+poly.eval(1)!= eval){
                printf("Error in %d\n",iter*k + i);
                exit(-1);
            }
            eval = poly.eval(a[i]);
            end = clock();
            vt += (double)(end - start)/(double)CLOCKS_PER_SEC; 
            
            for(int j = 0; j < L; j++){		
                data.poly[j] = data.poly[j] + a[i]*(data.poly[j+L]-data.poly[j]);
                beta[j] = beta[j] + a[i]*(beta[j+L]-beta[j]);
            }
        }
        
        iter++;
        data.FRI_poly[iter-1].resize(N/(1ULL<<(k*iter)));
        for(int i = 0; i < data.FRI_poly[iter-1].size(); i++){
            data.FRI_poly[iter-1][i] = data.poly[i];
        }
        change_form(data.FRI_poly[iter-1],(int)log2(data.FRI_poly[iter-1].size()),0,0);
        
        data.FRI_poly[iter-1].resize((2*N)/(1<<iter),F(0));
        fft(data.FRI_poly[iter-1],(int)log2(data.FRI_poly[iter-1].size()),false);
        //printf("%d\n",data.FRI_poly[iter-1].size());
        int queries = (int)(100.0/(log2(data.FRI_poly[iter-1].size()/(N/(1ULL<<(k*iter))))));
        //printf("Ratio : %d, Queries: %d\n",data.FRI_poly[iter-1].size()/(N/(1ULL<<(k*iter))),queries);
   
        F *buff = new F[data.FRI_poly[iter-1].size()];
        int counter = 0;
        
        for(int i = 0; i < data.FRI_poly[iter-1].size()/(1ULL<<k); i++){
            for(int j = 0; j < 1ULL<<k; j++){
                buff[counter++] = data.FRI_poly[iter-1][i+j*data.FRI_poly[iter-1].size()/(1ULL<<k)];
            }
        }
        
        merkle_tree::merkle_tree_prover::MT_commit_Blake(buff,data.FRI_MT[iter-1],data.FRI_poly[iter-1].size());
        delete[] buff;
        
        if((int)log2(N) - iter*k <= k){
            repeats = queries;
            remaining_size = 1ULL<<((int)log2(N) - iter*k);
            break;
        }
         // prepare for next iteration
        vector<vector<F>> z(repeats);
        vector<int> r;
        vector<F> y(repeats,F(0));
        compute_zetas(z,r,(int)log2(N) - iter*k,2*N/(1ULL<<(iter+k)));
        zetas.push_back(z);
        //compute_betas(betas,z);
        vector<F> _beta;
        for(int i = 0; i < y.size(); i++){
            precompute_beta(z[i],_beta);
            for(int j = 0; j <  _beta.size(); j++){
                y[i] += _beta[j]*data.poly[j];
            }
            _beta.clear();
        }
        F s = random();
        F pow = s;
        pows.push_back(pow);
        for(int i = 0; i  < repeats; i++){
            precompute_beta(z[i],_beta);
            for(int j  =0; j < _beta.size(); j++){
                beta[j] = beta[j] + pow*_beta[j];
            }
            _beta.clear();
            eval += pow*y[i];
            pow = pow*s;
        }
        _verify_iteration(data,a, r, repeats,iter, ps,vt);
        repeats = queries;
        challenge.insert(challenge.end(),a.begin(),a.end());
        a.clear();
    }
   
    // final verification step
    vector<F> final_poly(remaining_size),final_beta(remaining_size);
    for(int i = 0; i < remaining_size; i++){
        final_poly[i] = data.poly[i];
        final_beta[i] = beta[i];
    }
    ps += final_poly.size()*2*sizeof(F)/1024.0;
    F sum = 0;
    for(int i = 0; i < remaining_size; i++){
        sum += final_poly[i]*beta[i];
    }
    if(eval != sum){
        printf("Error in final verification step\n");
        exit(-1);
    }
    vector<vector<F>> z(repeats);
    vector<int> r;
    vector<F> y(repeats,F(0));
    a = generate_randomness((int)log2(remaining_size));
    challenge.insert(challenge.end(),a.begin(),a.end());
    compute_zetas(z,r,(int)log2(remaining_size),2*N/(1ULL<<(iter*k)));
    _verify_iteration(data,a, r, repeats,iter, ps,vt);
    eval = evaluate_vector(beta,a);
    for(int i = 0; i < zetas.size(); i++){
        vector<F> partial_challenge;
        vector<F> beta_evals;
        F pow = pows[i];
        for(int j = challenge.size() - zetas[i][0].size(); j < challenge.size(); j++){
            partial_challenge.push_back(challenge[j]);
        }
        for(int j  = 0; j < zetas[i].size(); j++){
            F prod = 1;

            for(int k = 0; k < zetas[i][j].size(); k++){
                prod *= ((zetas[i][j][k]*partial_challenge[k])+
                ((F(1)-zetas[i][j][k])*(F(1)-partial_challenge[k])));
            }
            eval -= pow*prod;
            pow *= pows[i];
        }
    }
    F prod = 1;
    for(int i = 0; i < x.size(); i++){
        prod *= (x[i]*challenge[i] + (F(1) - x[i])*(F(1)-challenge[i]));
    }
    eval -= prod;
    if(eval != F(0)){
        //printf("Error in betas verification\n");
    }
}

void whir_prove(PC_data &data, vector<F> x, double &vt, double &ps){
    
    
    aggregate(data, x, ps, vt);
    int rounds = (int)log2(data.aggr_poly.size());
    data.poly = data.aggr_poly;
   
    int k = 4;
    int N = data.poly.size();
    int repeats = 240;
    int iter = 0;
    clock_t start,end;
    
    data.FRI_poly.resize((int)log2(N)/k);
    data.FRI_MT.resize((int)log2(N)/k);
    
    vector<F> beta;
    vector<F> new_x;
    for(int i = 0; i < x.size()-4; i++){
        new_x.push_back(x[i]);
    }
    precompute_beta(new_x,beta);
    F eval = F(0);
    for(int i = 0; i < data.poly.size(); i++){
        eval += beta[i]*data.poly[i];
    }
    vector<F> a;
    
    while(true){
        for(int i = 0; i < k; i++){
            quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
            quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		    linear_poly l1,l2;
            int L = N/(1ULL<<(iter*k + (i+1)));
            for(int j = 0; j < L; j++){
                l1 = linear_poly(data.poly[j+L] - data.poly[j],data.poly[j]);
                l2 = linear_poly(beta[j+L] - beta[j],beta[j]);
                temp_poly = l1*l2;
                poly = poly + temp_poly;
            }
            ps+= (3*sizeof(F))/1024.0;
            start = clock();
            a.push_back(random());
            if(poly.eval(0)+poly.eval(1)!= eval){
                printf("Error in %d\n",iter*k + i);
                exit(-1);
            }
            eval = poly.eval(a[i]);
            end = clock();
            vt += (double)(end - start)/(double)CLOCKS_PER_SEC; 
            
            for(int j = 0; j < L; j++){		
                data.poly[j] = data.poly[j] + a[i]*(data.poly[j+L]-data.poly[j]);
                beta[j] = beta[j] + a[i]*(beta[j+L]-beta[j]);
            }
        }
        
        iter++;
        data.FRI_poly[iter-1].resize(N/(1ULL<<(k*iter)));
        for(int i = 0; i < data.FRI_poly[iter-1].size(); i++){
            data.FRI_poly[iter-1][i] = data.poly[i];
        }
        change_form(data.FRI_poly[iter-1],(int)log2(data.FRI_poly[iter-1].size()),0,0);
        //fft(data.FRI_poly[iter-1],(int)log2(data.FRI_poly[iter-1].size()),true);
        data.FRI_poly[iter-1].resize((2*N)/(1<<iter),F(0));
        fft(data.FRI_poly[iter-1],(int)log2(data.FRI_poly[iter-1].size()),false);
        F *buff = new F[data.FRI_poly[iter-1].size()];
        int counter = 0;
        for(int i = 0; i < data.FRI_poly[iter-1].size()/(1ULL<<k); i++){
            for(int j = 0; j < 1ULL<<k; j++){
                buff[counter++] = data.FRI_poly[iter-1][i+j*data.FRI_poly[iter-1].size()/(1ULL<<k)];
            }
        }
        
        merkle_tree::merkle_tree_prover::MT_commit(buff,data.FRI_MT[iter-1],data.FRI_poly[iter-1].size());
        delete[] buff;
        
        if((int)log2(N) - iter*k <= k || N/(1ULL<<(iter*k)) <= 2*repeats){
            break;
        }
         // prepare for next iteration
        vector<vector<F>> z(repeats);
        vector<int> r;
        vector<F> y(repeats,F(0));
        compute_zetas(z,r,(int)log2(N) - iter*k,2*N/(1ULL<<(iter*k)));
        //compute_betas(betas,z);
        vector<F> _beta;
        for(int i = 0; i < y.size(); i++){
            precompute_beta(z[i],_beta);
            for(int j = 0; j <  _beta.size(); j++){
                y[i] += _beta[j]*data.poly[j];
            }
            _beta.clear();
        }
        F s = random();
        F pow = s;
        for(int i = 0; i  < repeats; i++){
            precompute_beta(z[i],_beta);
            for(int j  =0; j < _beta.size(); j++){
                beta[j] = beta[j] + pow*_beta[j];
            }
            _beta.clear();
            eval += pow*y[i];
            pow = pow*s;
        }
        verify_iteration(data,a, r, repeats,iter, ps,vt);

        a.clear();
        
    }
    
}

void fri_prove(PC_data &data, vector<F> x){
    int rounds = (int)log2(data.poly.size())-10;
    double ps = 0.0,vt = 0.0;
    int N = data.poly.size()/2;
    int repeats = 100;
    clock_t s,e;
    
    data.FRI_poly.resize(rounds);
    data.FRI_MT.resize(rounds);
    for(int i = 0; i< rounds; i++){
        data.FRI_poly[i].resize(data.poly.size()/(1ULL<<(i+1)));
    }
    vector<F> beta;
    precompute_beta(x,beta);
    F eval = F(0);
    for(int i = 0; i < data.poly.size()/2; i++){
        eval += beta[i]*data.poly[i];
    }
    
    vector<F> a(rounds+1);
    for(int i = 0; i < rounds; i++){
        // first round sumcheck
	    quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		
        quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		linear_poly l1,l2;
	
        for(int j = 0; j < N/(1ULL<<(i+1)); j++){
            l1 = linear_poly(data.poly[2*j+1] - data.poly[2*j],data.poly[2*j]);
            l2 = linear_poly(beta[2*j+1] - beta[2*j],beta[2*j]);
            temp_poly = l1*l2;
            poly = poly + temp_poly;
        }
        
        ps+= (3*sizeof(F)+sizeof(__hhash_digest))/1024.0;
        s = clock();
        a[i] = random();
        a[i] = random();
        a[i] = random();
        poly.eval(0)+poly.eval(1);
        poly.eval(a[i]);
        e = clock();
        vt += (double)(e - s)/(double)CLOCKS_PER_SEC; 
        
        for(int j = 0; j < N/(1ULL<<(i+1)); j++){		
            data.poly[j] = data.poly[2*j] + a[i]*(data.poly[2*j+1]-data.poly[2*j]);
            beta[j] = beta[2*j] + a[i]*(beta[2*j+1]-beta[2*j]);
        }

        for(int j = 0; j < data.FRI_poly[i].size(); j++){
            if(i != 0){
                data.FRI_poly[i][j] = data.FRI_poly[i-1][2*j] + a[i]*data.FRI_poly[i-1][2*j+1];
            }else{
                data.FRI_poly[i][j] = data.poly[2*j] + a[i]*data.poly[2*j+1];
            }
        }
        
        merkle_tree::merkle_tree_prover::MT_commit(data.FRI_poly[i].data(),data.FRI_MT[i],data.FRI_poly[i].size());
    }
    a[rounds] = random();
    vector<F> msg(data.FRI_poly[rounds-1].size()/8);
    for(int i = 0; i < msg.size()/4; i++){
        msg[i] = data.FRI_poly[rounds-1][2*i] + a[rounds]*data.FRI_poly[rounds-1][2*i+1];
    }
    vector<int> random_points(repeats);
    vector<size_t> pos(2);
    vector<vector<__hhash_digest>> paths(repeats);
    ps+= msg.size()*sizeof(F)/1024.0;
    msg.resize(4*msg.size(),F(0));
    s = clock();
    fft(msg,(int)log2(msg.size()),false);    
    e = clock();
    vt += (double)(e-s)/(double)CLOCKS_PER_SEC;
    
    for(int i = 0; i < rounds; i++){
        bool *visited = new bool[2*data.FRI_poly[rounds-1-i].size()];
        for(int j = 0; j <2*data.FRI_poly[rounds-1-i].size(); j++){
            visited[j] = false;
        }
        for(int j = 0; j < repeats; j++){
            random_points[j] = rand()%(data.FRI_poly[rounds-1-i].size()/2);
        }
        for(int j = 0; j < repeats; j++){
            pos[0] = random_points[j];
            pos[1] = 0;
            paths[j] = merkle_tree::merkle_tree_prover::open_tree(data.FRI_MT[rounds-1-i],pos,0);
        }
        ps += 3*sizeof(F)/1024.0;
        //ps += repeats*sizeof(__hhash_digest)*paths[0].size()/1024.0;
        s = clock();
        for(int j = 0; j < repeats; j++){
            pos[0] = random_points[j];
            pos[1] = 0;
            merkle_tree::merkle_tree_verifier::verify_claim_opt(data.FRI_MT[rounds-1-i],paths[j].data(),random_points[j],data.FRI_poly[rounds-1-i].size(),visited,ps);
        }
        e = clock();
        vt += (double)(e-s)/(double)CLOCKS_PER_SEC;
    }
    printf("Ps : %lf, Vt : %lf\n", ps,vt);
}

FRI_proof fri(vector<F> arr, vector<vector<__hhash_digest>> &poly_hash, vector<vector<__hhash_digest>> &h_hash){
    
    
    
    FRI_proof P;
    int len = arr.size()/2;
    F one  = F(1);
    vector<vector<vector<__hhash_digest>>> fri_hashes;
    vector<vector<__hhash_digest>> temp_hash;
    while(len <= 128){
        temp_hash.clear();
        vector<F> com_arr(len);
        F r = F(rand());
        F omega = getRootOfUnity((int)log2(len) + 1);
        //F omega_pow;omega_pow.pow(omega_pow,omega,len);
        F omega_inv = omega.inv();
        F two_inv = F(2).inv(); 
        F b = F(1);
        for(int i = 0; i < len; i++){
            com_arr[i] = two_inv*(one + r*b)*arr[i] + (one - r*b)*arr[i+len];
            b = b*omega_inv;
        }
        MT_commit(com_arr,temp_hash,1);
        fri_hashes.push_back(temp_hash);
        len = len/2;
        arr = com_arr;
    }

    MT_proof path;
    vector<F> element;
    for(int i = 0; i < 120; i++){
        element.push_back(arr[i]);
        path = MT_Open(i,poly_hash);
        P.query_points.push_back(element);
        P.Proofs.push_back(path);
        path = MT_Open(i + arr.size()/2,poly_hash);
        P.query_points.push_back(element);
        P.Proofs.push_back(path);
        path = MT_Open(i,h_hash);
        P.query_points.push_back(element);
        P.Proofs.push_back(path);
        path = MT_Open(i + arr.size()/2,h_hash);
        P.query_points.push_back(element);
        P.Proofs.push_back(path);
        element.clear();
    }
    element.push_back(F(122));
            
    for(int j = 0; j < fri_hashes.size(); j++){
        for(int i = 0; i < 120; i++){
            path = MT_Open(i,fri_hashes[j]);
            P.query_points.push_back(element);
        
            P.Proofs.push_back(path);
            path = MT_Open(i+ fri_hashes[j][0].size()/2,fri_hashes[j]);
            P.query_points.push_back(element);
            P.Proofs.push_back(path);    
        }
        for(int i = 0; i < fri_hashes[j].size(); i++){
            vector<__hhash_digest>().swap(fri_hashes[j][i]);
        }
        vector<vector<__hhash_digest>>().swap(fri_hashes[j]);
    	fri_hashes[j].clear();
    }
        
    return P;



}

void prepare_data(vector<F> &encoded_poly, vector<F> &h, vector<F>  &LDT_arr, vector<vector<__hhash_digest>> &h_hashes, vector<F> r){
    vector<F> W;
    
    precompute_beta(r,W);
    fft(W, r.size(),true);
    W.resize(2*W.size(),0);
    fft(W,1 + r.size(),false);
    vector<F> lq(encoded_poly.size());
    h.resize(encoded_poly.size()/2);
    vector<F> prod(encoded_poly.size());
    for(int i = 0; i < encoded_poly.size(); i++){
        prod[i] = W[i]*encoded_poly[i];
    }
    fft(prod,r.size()+1,true);
    for(int i = 0; i < h.size(); i++){
        h[i] = prod[i+h.size()/2];
    }
    
    vector<F>().swap(prod);
	prod.clear();

    h.resize(encoded_poly.size(),F(0));
    fft(h,r.size()+1,false);
    
    MT_commit(h,h_hashes,1);    
    LDT_arr.resize(h.size());
    F rou = getRootOfUnity(log2(h.size()));
    F inv_x = F(1);
    F rou_n; 
   
    // check that!!!!
    rou_n = rou_n.fastPow(rou, h.size());
    F inv_rou;
    
    inv_rou = rou.inv();
    if(inv_rou*rou != F(1)){
        printf("Check inverse\n");
        exit(-1);
    }
    F x_n = F(1);
    F size = F(h.size());
    F const_sum = - (W[0] + encoded_poly[0]);
    for(int i = 0; i < h.size(); i++){
        F g = W[i] * encoded_poly[i ] - (x_n - 1) * h[i];
        LDT_arr[i] = (g + const_sum) *inv_x;
        inv_x = inv_x * inv_rou;
        x_n = x_n * rou_n;
    }
    fft(LDT_arr,r.size(),true);
}

Virgo_proof Virgo_open(vector<F> &poly,vector<F> &encoded_poly, vector<vector<__hhash_digest>> &hash_tree ,vector<F> r, int partitions){
    Virgo_proof P;
    vector<F> h,LDT_arr;
    vector<vector<__hhash_digest>> h_hashes,compressed_hashes;
    vector<vector<F>> aggr_elements(300);
    vector<MT_proof> aggregation_paths;
    if(partitions == 1){
        prepare_data(encoded_poly, h, LDT_arr, h_hashes, r);
    }else{
        
        vector<F> r1,r2;
        for(int i = 0; i < (int)log2(partitions); i++){r1.push_back(r[i]);}
        for(int i = (int)log2(partitions); i < r.size(); i++){r2.push_back(r[i]);}
       
        vector<F> beta;precompute_beta(r1,beta);
        F zero = F(0);
        vector<F> compressed_poly(encoded_poly.size()/partitions,zero);
        for(int i = 0; i < compressed_poly.size()/partitions; i++){
            for(int j = 0; j < partitions; j++){
                if(i < 150) aggr_elements[2*i].push_back(encoded_poly[i*partitions + j]);
                compressed_poly[j] += beta[j]*encoded_poly[i*partitions + j];
                if(i < 150) aggr_elements[2*i+1].push_back(compressed_poly[j]);
                
            }
        }
        MT_commit(compressed_poly,compressed_hashes,1);
        for(int i = 0; i < 150; i++){
            aggregation_paths.push_back(MT_Open(i,hash_tree));
            aggregation_paths.push_back(MT_Open(i,compressed_hashes));
        }
        prepare_data(compressed_poly, h, LDT_arr, h_hashes, r2);
  
    }
    
    FRI_proof FRI_P = fri(LDT_arr,hash_tree,h_hashes);
    P.Fri = FRI_P;
    P.query_paths = aggregation_paths;  
    P.query_points = aggr_elements;
    // need to put sumcheck for W
   
    return P;
}
