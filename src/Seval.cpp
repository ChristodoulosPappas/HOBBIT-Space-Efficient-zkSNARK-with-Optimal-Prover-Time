#include "config_pc.hpp"
#include "utils.hpp"
#include "Seval.h"
#include <thread>
#include <mutex>

extern mutex mtx,mtx2;
extern int fun;
extern size_t input_size;
extern int depth;
extern tr_tuple *tr;
extern int BUFFER_SPACE_tr;
int labels = 1;
int ct = 0;
int domain = 16;
double prune_rate;
vector<vector<int>> lookup_table;
extern vector<int> layer_size;

void init_gate(gt &g, F v){
    g.value = v;
    g.idx = labels++;
    g.access = 0;
}

void create_xor_table(int idx){
    lookup_table[idx].resize(1ULL<<16);
    for(int i = 0; i < 256; i++){
        for(int j = 0; j < 256; j++){
            lookup_table[idx][256*i + j] = i^j;
        }
    }
}

void create_eq_table(int idx){
    lookup_table[idx].resize(1ULL<<16);
    for(int i = 0; i < 256; i++){
        for(int j = 0; j < 256; j++){
            lookup_table[idx][256*i + j] = 0;
            if(j == i){
                lookup_table[idx][256*i + j] = 1;
            }
        }
    }
}

void create_ltu_table(int idx){
    lookup_table[idx].resize(1ULL<<16);
    for(int i = 0; i < 256; i++){
        for(int j = 0; j < 256; j++){
            lookup_table[idx][256*i + j] = 0;
            if(i < j){
                lookup_table[idx][256*i + j] = 1;
            }
        }
    }
}

void create_Sbox(int idx){
    lookup_table[idx].resize(1ULL<<8);
    for(int i = 0; i < 256; i++){
        lookup_table[idx][i] = (i+21)%256;
    }
}

void create_MixBox(int idx){
    lookup_table[idx].resize(1ULL<<8);
    for(int i = 0; i < 256; i++){
        lookup_table[idx][i] = (i+idx)%256;
    }
}

//Not accurate, just for the experiments
void create_Lshift_tables(int idx){
    for(int i = idx; i < idx+4; i++){
        lookup_table[i].resize(32*256);
        for(int j = 0; j < 32; j++){
            for(int k = 0; k < 256; k++){
                lookup_table[i][256*j + k] = k<<j;
            }
        }
    }
}

//Not accurate, just for the experiments
void create_Rshift_tables(int idx){
    for(int i = idx; i < idx+4; i++){
        lookup_table[i].resize(32*256);
        for(int j = 0; j < 32; j++){
            for(int k = 0; k < 256; k++){
                lookup_table[i][256*j + k] = ((1ULL<<(i-idx+1))*k)>>j;
            }
        }
    }
}

void delete_gate(gt &g){
    // write in buffer    
    
    
    tr[ct].type =0;
    tr[ct].idx_o =g.idx;
    tr[ct].value_o =g.value;
    tr[ct].access_o =g.access;
    
    ct++;
    if(BUFFER_SPACE_tr == ct){
        ct = 0;
        // semaphore down
        mtx2.unlock();
        mtx.lock();
    }
}





gt add_gate(gt &g1,gt &g2){
    gt g; 
    g.value = g1.value+g2.value;
    g.idx = labels++;
    g.access = 0;
    //init_gate(g,g1.value+g2.value);
    // write in buffer
    
    tr[ct].type = 1;
    tr[ct].idx_o = g.idx;
    tr[ct].value_o = g.value;
    tr[ct].idx_l = g1.idx;
    tr[ct].value_l = g1.value;
    tr[ct].idx_r = g2.idx;
    tr[ct].value_r = g2.value;
    tr[ct].access_l = g1.access;
    g1.access++;
    tr[ct].access_r = g2.access;
    tr[ct].access_o = 0;
    g2.access++;
    g.access = 1;
    /*
    
    tr[ct] = t;
    */
    
    ct++;
    if(BUFFER_SPACE_tr == ct){
        ct = 0;
        // semaphore down
        mtx2.unlock();
        mtx.lock();
    }
    return g;
}

gt mul_gate(gt &g1,gt &g2){
    gt g; 
    g.value = g1.value*g2.value;
    g.idx = labels++;
    g.access = 0;
    //init_gate(g,g1.value*g2.value);
  
    tr[ct].type = 2;
    tr[ct].idx_o = g.idx;
    tr[ct].value_o = g.value;
    tr[ct].idx_l = g1.idx;
    tr[ct].value_l = g1.value;
    tr[ct].idx_r = g2.idx;
    tr[ct].value_r = g2.value;
    tr[ct].access_l = g1.access;
    g1.access++;
    tr[ct].access_r = g2.access;
    tr[ct].access_o = 0;
    g2.access++;
    g.access = 1;
    
    /*
    tr[ct] = t;
    */
    
    // write in buffer
    ct++;
    if(BUFFER_SPACE_tr == ct){
        ct = 0;
        // semaphore down
        mtx2.unlock();
        mtx.lock();
    }
    return g;
}
gt lookup_gate(gt &g1,gt &g2, int table_id){
    gt g; 
    // Rangeproof
    if(table_id == 3){
        g.value = g1.value;
    }else{
        g.value = lookup_table[table_id-3][g1.value.real + 256*g2.value.real];
    }
    g.idx = labels++;
    g.access = 0;

    tr[ct].type = table_id;
    tr[ct].idx_o = g.idx;
    tr[ct].value_o = g.value;
    tr[ct].idx_l = g1.idx;
    tr[ct].value_l = g1.value;
    tr[ct].idx_r = g2.idx;
    tr[ct].value_r = g2.value;
    tr[ct].access_l = g1.access;
    g1.access++;
    tr[ct].access_r = g2.access;
    tr[ct].access_o = 0;
    g2.access++;
    g.access = 1;
    ct++;
    if(BUFFER_SPACE_tr == ct){
        ct = 0;
        // semaphore down
        mtx2.unlock();
        mtx.lock();
    }
    return g;
}
gt ltu_gate(vector<gt> &bytes1,vector<gt> &bytes2, int idx){
    vector<gt> ltu_arr(bytes1.size());
    for(int i = 0; i < bytes1.size(); i++){
        init_gate(ltu_arr[i],F(lookup_table[idx][bytes1[i].value.real + 256*bytes2[i].value.real]));
        tr[ct].type = idx+3;
        tr[ct].idx_o = ltu_arr[i].idx;
        tr[ct].value_o = ltu_arr[i].value;
        tr[ct].idx_l = bytes1[i].idx;
        tr[ct].value_l = bytes1[i].value;
        tr[ct].idx_r = bytes2[i].idx;
        tr[ct].value_r = bytes2[i].value;
        tr[ct].access_l = bytes1[i].access;
        bytes1[i].access++;
        tr[ct].access_r = bytes2[i].access;
        tr[ct].access_o = 0;
        bytes2[i].access++;
        ltu_arr[i].access = 1;
        ct++;
        if(BUFFER_SPACE_tr == ct){
            ct = 0;
            // semaphore down
            mtx2.unlock();
            mtx.lock();
        }
    }
    vector<gt> eq_arr(bytes1.size()-1);
    for(int i = 0; i < eq_arr.size(); i++){
        init_gate(eq_arr[i],F(lookup_table[idx+1][bytes1[i].value.real + 256*bytes2[i].value.real]));
        tr[ct].type = idx+4;
        tr[ct].idx_o = eq_arr[i].idx;
        tr[ct].value_o = eq_arr[i].value;
        tr[ct].idx_l = bytes1[i].idx;
        tr[ct].value_l = bytes1[i].value;
        tr[ct].idx_r = bytes2[i].idx;
        tr[ct].value_r = bytes2[i].value;
        tr[ct].access_l = bytes1[i].access;
        bytes1[i].access++;
        tr[ct].access_r = bytes2[i].access;
        tr[ct].access_o = 0;
        bytes2[i].access++;
        eq_arr[i].access = 1;
        ct++;
        if(BUFFER_SPACE_tr == ct){
            ct = 0;
            // semaphore down
            mtx2.unlock();
            mtx.lock();
        }
    }
    for(int i = eq_arr.size()-2; i >= 0; i--){
        gt temp_prod = mul_gate(eq_arr[i],eq_arr[i+1]);
        delete_gate(eq_arr[i]);
        eq_arr[i] = temp_prod;
    }
    gt out = mul_gate(eq_arr[0],ltu_arr[0]);
    for(int i = 1; i < eq_arr.size()-1; i++){
        gt temp_prod = mul_gate(eq_arr[i],ltu_arr[i]);
        gt temp_out = add_gate(out,temp_prod);
        delete_gate(out);
        delete_gate(temp_prod);
        out = temp_out;
    }
    gt temp_out = add_gate(out,ltu_arr[ltu_arr.size()-1]);
    delete_gate(out);
    out = temp_out;
    for(int i = 0; i < ltu_arr.size(); i++){
        delete_gate(ltu_arr[i]);
    }
    for(int i = 0; i < eq_arr.size(); i++){
        delete_gate(eq_arr[i]);
    }
    return out;
}
vector<gt> xor_word(vector<gt> &bytes1, vector<gt> &bytes2, int table_id){
    vector<gt> out(bytes1.size());
    for(int i = 0; i < out.size(); i++){
        init_gate(out[i],F(lookup_table[table_id][bytes1[i].value.real + 256*bytes2[i].value.real]));
        tr[ct].type = 4;
        tr[ct].idx_o = out[i].idx;
        tr[ct].value_o = out[i].value;
        tr[ct].idx_l = bytes1[i].idx;
        tr[ct].value_l = bytes1[i].value;
        tr[ct].idx_r = bytes2[i].idx;
        tr[ct].value_r = bytes2[i].value;
        tr[ct].access_l = bytes1[i].access;
        bytes1[i].access++;
        tr[ct].access_r = bytes2[i].access;
        tr[ct].access_o = 0;
        bytes2[i].access++;
        out[i].access = 1;
        ct++;
        if(BUFFER_SPACE_tr == ct){
            ct = 0;
            // semaphore down
            mtx2.unlock();
            mtx.lock();
        }
    }
    return out;
}

gt xor_gate(gt &bytes1, gt &bytes2, int table_id){
    gt out;
    //for(int i = 0; i < out.size(); i++){
        if(lookup_table[table_id].size() <= (bytes1.value.real + 256*bytes2.value.real)){
            printf("Errror xor %d\n",bytes1.value.real + 256*bytes2.value.real);
            exit(-2);
        }
        init_gate(out,F(lookup_table[table_id][bytes1.value.real + 256*bytes2.value.real]));
        tr[ct].type = table_id+3;
        tr[ct].idx_o = out.idx;
        tr[ct].value_o = out.value;
        tr[ct].idx_l = bytes1.idx;
        tr[ct].value_l = bytes1.value;
        tr[ct].idx_r = bytes2.idx;
        tr[ct].value_r = bytes2.value;
        tr[ct].access_l = bytes1.access;
        bytes1.access++;
        tr[ct].access_r = bytes2.access;
        tr[ct].access_o = 0;
        bytes2.access++;
        out.access = 1;
        ct++;
        if(BUFFER_SPACE_tr == ct){
            ct = 0;
            // semaphore down
            mtx2.unlock();
            mtx.lock();
        }
    //}
    return out;
}

gt right_shift(vector<gt> &word, vector<gt> &right_shift_pows, gt &offset_r, int idx){
    vector<gt> right_shift_bytes(word.size());
    for(int i = 0; i < word.size(); i++){
        init_gate(right_shift_bytes[i],F(lookup_table[idx+i][256*offset_r.value.real+word[i].value.real]));
        tr[ct].type = idx+i+word.size();
        tr[ct].idx_o = right_shift_bytes[i].idx;
        tr[ct].value_o = right_shift_bytes[i].value;
        
        tr[ct].idx_l = word[i].idx; 
        tr[ct].value_l = word[i].value; 
        
        tr[ct].idx_r = offset_r.idx;
        tr[ct].value_r = offset_r.value;
        
        tr[ct].access_r = offset_r.access;
        offset_r.access++;
        tr[ct].access_l = word[i].access;
        tr[ct].access_o = 0;
        word[i].access++;
        right_shift_bytes[i].access = 1;
        ct++;
        if(BUFFER_SPACE_tr == ct){
            ct = 0;
            // semaphore down
            mtx2.unlock();
            mtx.lock();
        }
    }

    gt sum = mul_gate(right_shift_pows[0],right_shift_bytes[0]);
    for(int i = 1; i < right_shift_pows.size(); i++){
        gt temp_mul = mul_gate(right_shift_pows[i],right_shift_bytes[i]);
        gt temp_sum = add_gate(sum,temp_mul);
        delete_gate(sum);
        delete_gate(temp_mul);
        sum = temp_sum;
    }
    for(int i = 0; i < right_shift_bytes.size(); i++){
        delete_gate(right_shift_bytes[i]);
    }
    return sum;
}

gt circular_shift(vector<gt> &word, vector<gt> &left_shift_pows,vector<gt> &right_shift_pows, gt &offset_r, gt &offset_l, int idx){
    vector<gt> left_shift_bytes(word.size());
    vector<gt> right_shift_bytes(word.size());
    for(int i = 0; i < word.size(); i++){
        init_gate(left_shift_bytes[i],F(lookup_table[idx+i][256*offset_l.value.real+word[i].value.real]));
        tr[ct].type = idx+i+3;
        tr[ct].idx_o = left_shift_bytes[i].idx;
        tr[ct].value_o = left_shift_bytes[i].value;
        
        tr[ct].idx_l = word[i].idx;
        tr[ct].value_l = word[i].value; 
        
        tr[ct].idx_r = offset_l.idx;
        tr[ct].value_r = offset_l.value;
        
        tr[ct].access_r = offset_l.access;
        offset_l.access++;
        tr[ct].access_l = word[i].access;
        tr[ct].access_o = 0;
        word[i].access++;
        left_shift_bytes[i].access = 1;
        ct++;
        if(BUFFER_SPACE_tr == ct){
            ct = 0;
            // semaphore down
            mtx2.unlock();
            mtx.lock();
        }
    }


    for(int i = 0; i < word.size(); i++){
        init_gate(right_shift_bytes[i],F(lookup_table[idx+i+word.size()][256*offset_r.value.real+word[i].value.real]));
        tr[ct].type = idx+i+word.size()+3;
        tr[ct].idx_o = right_shift_bytes[i].idx;
        tr[ct].value_o = right_shift_bytes[i].value;
        
        tr[ct].idx_l = word[i].idx; 
        tr[ct].value_l = word[i].value; 
        
        tr[ct].idx_r = offset_r.idx;
        tr[ct].value_r = offset_r.value;
        
        tr[ct].access_r = offset_r.access;
        offset_r.access++;
        tr[ct].access_l = word[i].access;
        tr[ct].access_o = 0;
        word[i].access++;
        right_shift_bytes[i].access = 1;
        ct++;
        if(BUFFER_SPACE_tr == ct){
            ct = 0;
            // semaphore down
            mtx2.unlock();
            mtx.lock();
        }
    }

    gt sum = mul_gate(left_shift_pows[0],left_shift_bytes[0]);
    for(int i = 1; i < left_shift_pows.size(); i++){
        gt temp_mul = mul_gate(left_shift_pows[i],left_shift_bytes[i]);
        gt temp_sum = add_gate(sum,temp_mul);
        delete_gate(sum);
        delete_gate(temp_mul);
        sum = temp_sum;
    }
    gt sum_left = sum;
    sum = mul_gate(right_shift_pows[0],right_shift_bytes[0]);
    for(int i = 1; i < right_shift_pows.size(); i++){
        gt temp_mul = mul_gate(right_shift_pows[i],right_shift_bytes[i]);
        gt temp_sum = add_gate(sum,temp_mul);
        delete_gate(sum);
        delete_gate(temp_mul);
        sum = temp_sum;
    }
    gt out = add_gate(sum,sum_left);
    delete_gate(sum);
    delete_gate(sum_left);
    for(int i = 0; i < left_shift_bytes.size(); i++){
        delete_gate(left_shift_bytes[i]);
        delete_gate(right_shift_bytes[i]);
    }
    return out;
}



void fun1(vector<gt> &input){
    for(int i = 0; i < depth; i++){
        for(int j =  0; j < input.size(); j++){
            if(i % 3 == 0){
                gt g = add_gate(input[j],input[j]);
                delete_gate(input[j]);
                input[j] = g;
            }else{
                gt g = mul_gate(input[j],input[j]);
                delete_gate(input[j]);
                input[j] = g;
            }
        }
    }
    for(int j = 0; j < input.size(); j++){
        delete_gate(input[j]);
    }
    
    tr_tuple t;
    t.type = 255;
    t.idx_o = -1;
    t.value_o = -1;
    labels = 1;
    tr[ct] = t;
    // write in buffer
    ct = 0;
    mtx2.unlock();
    mtx.lock();
    
}

void _fun1(vector<gt> &input){
    for(int i = 0; i < depth; i++){
        for(int j =  0; j < input.size(); j++){
            if(i % 3 == 0){
                gt g;g.value = input[j].value + input[j].value;//(input[j],input[j]);
                //delete_gate(input[j]);
                input[j] = g;
            }else{
                gt g;g.value = input[j].value*input[j].value;//mul_gate(input[j],input[j]);
                //delete_gate(input[j]);
                input[j] = g;
            }
        }
    }
}


void get_circuit_info(size_t &gates, size_t &ops){
    if(fun == 2){
        gates =0;
        ops = 0;
        gates += input_size+3;
        gates += input_size*8;
        ops += input_size*6;        
    }
    if(fun == 3){
        gates = 0;
        ops = 0;
        gates = 33+input_size*32*5;
        ops = input_size*32*4;
    }
}

void Seval(){
    if(fun == 1){
        vector<gt> input(input_size);
        for(int i = 0; i < input.size(); i++){
                init_gate(input[i],F(3221*i+1));
            }
         
            _fun1(input);
        
    }
    if(fun == 2){
        vector<gt> pows(2),input(input_size);
        //init_gate(pows[0],F(1));
        //init_gate(pows[1],F(1<<16));
        for(int i = 0; i < input_size; i++){
        //    init_gate(input[i],F(rand()%(1<<21))); 
        }
        //_range_proof(input,pows);
    }
    labels = 1;
}

void range_proof_naive(vector<gt> &pows, vector<gt> &input){
    gt one;
    init_gate(one,F(-1));
    for(int i = 0; i < input.size(); i++){
        vector<gt> aux_bits(pows.size());
        vector<int> bits;
        int v = input[i].value.real;
        for(int j = 0; j < pows.size(); j++){
            bits.push_back(v&1);
            v = v>>1;
            init_gate(aux_bits[j],F(v));
        }
        for(int j = 0; j < pows.size(); j++){
            gt add = add_gate(one,aux_bits[j]);
            gt _z = mul_gate(add,aux_bits[j]);
            delete_gate(add);
            delete_gate(_z);
        }
        gt sum = mul_gate(aux_bits[0],pows[0]);
        for(int j = 1; j < pows.size(); j++){
            gt prod = mul_gate(aux_bits[j],pows[j]);
            gt temp_sum = add_gate(sum,prod);
            delete_gate(prod);
            delete_gate(sum);
            sum = temp_sum;
        }
        delete_gate(sum);
        for(int j = 0; j < aux_bits.size(); j++){
            delete_gate(aux_bits[j]);
        }
    }

    for(int i = 0; i < input.size(); i++){
        delete_gate(input[i]);
    }
    for(int i = 0; i < pows.size(); i++){
        delete_gate(pows[i]);
    }
    delete_gate(one);
    tr_tuple t;
    t.type = 255;
    t.idx_o = -1;
    t.value_o = -1;
    labels = 1;
    tr[ct] = t;
    // write in buffer
    ct = 0;
    mtx2.unlock();
    mtx.lock();
    
}

void range_proof(vector<gt> &pows, vector<gt> &input){
    gt zero;init_gate(zero,F(0));
    for(int i = 0; i < input.size(); i++){
        int v1,v2;
        v1 = input[i].value.real%(1<<16);
        v2 = input[i].value.real>>16;
        gt aux1,aux2;
        init_gate(aux1,F(v1));
        init_gate(aux2,F(v2));
        gt lookup_aux1 = lookup_gate(aux1,zero,3);
        delete_gate(aux1);
        gt lookup_aux2 = lookup_gate(aux2,zero,3);
        delete_gate(aux2); 
        gt t1 = mul_gate(pows[0],lookup_aux1);
        gt t2 = mul_gate(pows[1],lookup_aux2);
        gt t3 = add_gate(t1,t2);
        gt t4 = add_gate(input[i],t3);
        delete_gate(lookup_aux1);
        delete_gate(lookup_aux2);
        delete_gate(t1);
        delete_gate(t2);
        delete_gate(t3);
        delete_gate(t4);
    }
    for(int i = 0; i < pows.size(); i++){
        delete_gate(pows[i]);
    }
    for(int i = 0 ;i < input.size(); i++){
        delete_gate(input[i]);
    }
    delete_gate(zero);
    tr_tuple t;
    t.type = 255;
    t.idx_o = -1;
    t.value_o = -1;
    labels = 1;
    tr[ct] = t;
    // write in buffer
    ct = 0;
    mtx2.unlock();
    mtx.lock();
}

vector<gt> get_bytes(gt &word, vector<gt> &range_table, vector<gt> &pows, gt &zero){
    vector<gt> bytes(domain/8);
    unsigned int v = word.value.real;
    
    for(int i = 0; i < domain/8; i++){
        bytes[i] = lookup_gate(range_table[v%256],zero,3);
        v = v>>8;
    }
    
    
    gt check = mul_gate(pows[0],bytes[0]);
    for(int i = 1; i < domain/8; i++){
        gt temp_prod = mul_gate(pows[i],bytes[i]);
        gt temp_check = add_gate(check,temp_prod);
        delete_gate(check);
        delete_gate(temp_prod);
        check = temp_check;
    }
    delete_gate(check);
    return bytes;
}

void compute_hash(vector<gt> &words, vector<gt> &pp,vector<gt> &left_rotations, 
        vector<gt> &right_rotations, vector<gt> &left_shift_pows, vector<gt> &right_shift_pows, vector<gt> &shifts,
        vector<gt> &range_table, vector<gt> &pows, gt &zero){
    
    vector<gt> total_words(64);
    for(int i = 0; i < words.size(); i++){
        total_words[i] = words[i];
    }
    vector<vector<gt>> words_bytes(64);
    
    for(int i = 0; i < words.size(); i++){
        words_bytes[i] = get_bytes(words[i],range_table,pows,zero);
    }
    printf("%d\n",labels);
    for(int i = 16; i < 64; i++){
        gt s01 = circular_shift(words_bytes[i-15],left_shift_pows,right_shift_pows,right_rotations[0],left_rotations[0],2);
        gt s02 = circular_shift(words_bytes[i-15],left_shift_pows,right_shift_pows,right_rotations[1],left_rotations[1],2);
        gt s03 = right_shift(words_bytes[i-15],right_shift_pows,shifts[0],6);
        gt s11 = circular_shift(words_bytes[i-2],left_shift_pows,right_shift_pows,right_rotations[2],left_rotations[2],2);
        gt s12 = circular_shift(words_bytes[i-2],left_shift_pows,right_shift_pows,right_rotations[3],left_rotations[3],2);
        gt s13 = right_shift(words_bytes[i-2],right_shift_pows,shifts[1],6);
        vector<gt> s01_bytes,s02_bytes,s03_bytes,s11_bytes,s12_bytes,s13_bytes;
        s01_bytes = get_bytes(s01,range_table,pows,zero);
        s02_bytes = get_bytes(s02,range_table,pows,zero);
        s03_bytes = get_bytes(s03,range_table,pows,zero);
        s11_bytes = get_bytes(s11,range_table,pows,zero);
        s12_bytes = get_bytes(s12,range_table,pows,zero);
        s13_bytes = get_bytes(s13,range_table,pows,zero);
        vector<gt> temp_s0 = xor_word(s01_bytes,s02_bytes,1);
        vector<gt> s0 = xor_word(s03_bytes,temp_s0,1);
        vector<gt> temp_s1 = xor_word(s11_bytes,s12_bytes,1);
        vector<gt> s1 = xor_word(s13_bytes,temp_s1,1);
        vector<gt> s(s1.size());
        for(int j = 0; j < s.size(); j++){
            s[j] = add_gate(s0[j],s1[j]);
        }
        gt sum = mul_gate(pows[0],s[0]);
        for(int j = 1; j < 4; j++){
            gt temp_prod = mul_gate(pows[j],s[j]);
            gt temp_sum = add_gate(sum,temp_prod);
            delete_gate(sum);
            delete_gate(temp_prod);
            sum = temp_sum;
        }
        
        gt temp_sum = add_gate(sum,total_words[i-16]);
        delete_gate(sum);
        total_words[i] = add_gate(temp_sum,total_words[i-7]);
        delete_gate(temp_sum);
        words_bytes[i] = get_bytes(words[i],range_table,pows,zero);
        delete_gate(s01);delete_gate(s02);delete_gate(s03);
        delete_gate(s11);delete_gate(s12);delete_gate(s13);
        for(int j = 0; j < temp_s0.size(); j++){
            delete_gate(s[j]);
            delete_gate(temp_s0[j]);delete_gate(temp_s1[j]);
            delete_gate(s0[j]);delete_gate(s1[j]);     
            delete_gate(s01_bytes[j]);delete_gate(s02_bytes[j]);delete_gate(s03_bytes[j]);
            delete_gate(s11_bytes[j]);delete_gate(s12_bytes[j]);delete_gate(s13_bytes[j]);
        }
    }
    for(int i = 16; i < total_words.size(); i++){
        delete_gate(total_words[i]);
    }
    for(int i  =0; i < words_bytes.size(); i++){
        for(int j  =0 ; j < words_bytes[i].size(); j++){
            delete_gate(words_bytes[i][j]);
        }
    }
    vector<gt> working_variables(8);
    vector<gt> temp_working_variables(8);
    for(int i = 0; i < 8; i++){
        init_gate(working_variables[i],F(323+i));
    }
    vector<vector<gt>> working_bytes(working_variables.size()),temp_working_bytes(8);

    for(int i = 0; i < 8; i++){
        working_bytes[i] = get_bytes(working_variables[i],range_table,pows,zero);
    }
    for(int i = 0; i < 64; i++){

        gt s01 = circular_shift(working_bytes[4],left_shift_pows,right_shift_pows,right_rotations[4],left_rotations[4],2);
        gt s02 = circular_shift(working_bytes[4],left_shift_pows,right_shift_pows,right_rotations[5],left_rotations[5],2);
        gt s03 = circular_shift(working_bytes[4],left_shift_pows,right_shift_pows,right_rotations[6],left_rotations[6],2);
        gt s11 = circular_shift(working_bytes[0],left_shift_pows,right_shift_pows,right_rotations[7],left_rotations[7],2);
        gt s12 = circular_shift(working_bytes[0],left_shift_pows,right_shift_pows,right_rotations[8],left_rotations[8],2);
        gt s13 = circular_shift(working_bytes[0],left_shift_pows,right_shift_pows,right_rotations[9],left_rotations[9],2);  
        vector<gt> s01_bytes,s02_bytes,s03_bytes,s11_bytes,s12_bytes,s13_bytes;
        s01_bytes = get_bytes(s01,range_table,pows,zero);
        s02_bytes = get_bytes(s02,range_table,pows,zero);
        s03_bytes = get_bytes(s03,range_table,pows,zero);
        s11_bytes = get_bytes(s11,range_table,pows,zero);
        s12_bytes = get_bytes(s12,range_table,pows,zero);
        s13_bytes = get_bytes(s13,range_table,pows,zero);
        vector<gt> temp_s0 = xor_word(s01_bytes,s02_bytes,1);
        vector<gt> s0 = xor_word(s03_bytes,temp_s0,1);
        vector<gt> temp_s1 = xor_word(s11_bytes,s12_bytes,1);
        vector<gt> s1 = xor_word(s13_bytes,temp_s1,1);
        
        vector<gt> temp_ch1 = xor_word(working_bytes[4],working_bytes[5],1);
        vector<gt> temp_ch2 = xor_word(working_bytes[4],working_bytes[6],1);
        vector<gt> ch = xor_word(temp_ch1,temp_ch2,1);

        vector<gt> temp_maj1 = xor_word(working_bytes[0],working_bytes[1],1);
        vector<gt> temp_maj2 = xor_word(working_bytes[0],working_bytes[2],1);
        vector<gt> temp_maj3 = xor_word(working_bytes[1],working_bytes[2],1);
        vector<gt> temp_maj4 = xor_word(temp_maj1,temp_maj2,1);
        vector<gt> maj = xor_word(temp_maj4,temp_maj3,1); 
        vector<gt> temp1_bytes(maj.size()),temp2_bytes(maj.size());
        for(int j  = 0; j < temp1_bytes.size(); j++){
            temp1_bytes[j] = add_gate(s0[j],ch[j]);
            temp2_bytes[j] = add_gate(s1[j],maj[j]);
        }
        gt temp1 = mul_gate(pows[0],temp1_bytes[0]);
        for(int j = 1; j < temp1_bytes.size(); j++){
            gt temp_prod = mul_gate(pows[j],temp1_bytes[j]);
            gt temp_sum = add_gate(temp_prod,temp1);
            delete_gate(temp_prod);
            delete_gate(temp1);
            temp1 = temp_sum;
        }
        gt temp2 = mul_gate(pows[0],temp2_bytes[0]);
        for(int j = 1; j < temp1_bytes.size(); j++){
            gt temp_prod = mul_gate(pows[j],temp2_bytes[j]);
            gt temp_sum = add_gate(temp_prod,temp2);
            delete_gate(temp_prod);
            delete_gate(temp2);
            temp2 = temp_sum;
        }
        gt temp_sum = add_gate(pp[i],temp1);
        delete_gate(temp1);
        temp1 = temp_sum;
        temp_sum = add_gate(total_words[i],temp1);
        delete_gate(temp1);
        temp1 = temp_sum;  
        temp_sum = add_gate(temp_working_variables[7],temp1);
        delete_gate(temp1);
        temp1 = temp_sum; 

        temp_working_variables[0] = working_variables[6];
        temp_working_bytes[0] = working_bytes[6];
        temp_working_variables[1] = working_variables[5];
        temp_working_bytes[1] = working_bytes[5];
        temp_working_variables[2] = working_variables[4];
        temp_working_bytes[2] = working_bytes[4];
        temp_working_variables[3] = add_gate(working_variables[3],temp1);
        temp_working_bytes[3] = get_bytes(temp_working_variables[3],range_table,pows,zero);
        temp_working_variables[4] = working_variables[2];
        temp_working_bytes[4] = working_bytes[2];
        temp_working_variables[5] = working_variables[1];
        temp_working_bytes[5] = working_bytes[1];
        temp_working_variables[6] = working_variables[0];
        temp_working_bytes[6] = working_bytes[0];
        temp_working_variables[7] = add_gate(temp1,temp2);
        temp_working_bytes[7] = get_bytes(temp_working_variables[7],range_table,pows,zero);
        
        delete_gate(working_variables[0]);delete_gate(working_variables[4]);
        for(int j = 0; j < working_bytes[0].size(); j++){
            delete_gate(working_bytes[0][j]);
            delete_gate(working_bytes[4][j]);
        }

        delete_gate(temp1);delete_gate(temp2);

        for(int j = 0; j < working_variables.size(); j++){
            working_variables[7-j] = temp_working_variables[j];
            working_bytes[7-j] = temp_working_bytes[j];
        }

        delete_gate(s01);delete_gate(s03);delete_gate(s02);
        delete_gate(s11);delete_gate(s12); delete_gate(s13);
        for(int j = 0; j < s11_bytes.size(); j++){
            delete_gate(s01_bytes[j]);delete_gate(s02_bytes[j]);delete_gate(s03_bytes[j]);
            delete_gate(s11_bytes[j]);delete_gate(s12_bytes[j]);delete_gate(s13_bytes[j]);
            delete_gate(temp_s0[j]);delete_gate(temp_s1[j]);
            delete_gate(s1[j]);delete_gate(s0[j]);
            delete_gate(temp_ch1[j]);delete_gate(temp_ch2[j]);delete_gate(ch[j]);
            delete_gate(temp_maj1[j]);delete_gate(temp_maj2[j]);delete_gate(temp_maj3[j]);
            delete_gate(temp_maj4[j]);delete_gate(maj[j]);
            delete_gate(temp1_bytes[j]);delete_gate(temp2_bytes[j]);
        }     
    }
    for(int i  =0; i < working_bytes.size(); i++){
        for(int j = 0; j < working_bytes[i].size(); j++){
            delete_gate(working_bytes[i][j]);
        }
    }
    for(int i = 0 ;i < working_variables.size(); i++){
        delete_gate(working_variables[i]);
    }  
}

void dummy_comp(gt &x){
    for(int i = 0; i < input_size*(depth+1)-1; i++){
        gt temp = add_gate(x,x);
        delete_gate(x);
        x = temp;
    }
    delete_gate(x);
    tr_tuple t;
    t.type = 255;
    t.idx_o = -1;
    t.value_o = -1;
    labels = 1;
    tr[ct] = t;
    // write in buffer
    ct = 0;
    mtx2.unlock();
    mtx.lock();   

}

void SHA256(vector<vector<gt>> &input, vector<gt> &pp,vector<gt> &left_rotations, 
        vector<gt> &right_rotations, vector<gt> &left_shift_pows, vector<gt> &right_shift_pows, vector<gt> &shifts){
    gt zero;
    vector<gt> range_table(256);
    vector<gt> pows(4);
    for(int i = 0; i < 256; i++){
        init_gate(range_table[i],F(i));
    }
    for(int i = 0; i < 4; i++){
        init_gate(pows[i],F(1ULL<<(i*8)));
    }
    init_gate(zero,F(0));
    for(int i = 0; i < input.size(); i++){
        compute_hash(input[i],pp,left_rotations,right_rotations,left_shift_pows,right_shift_pows,shifts,range_table,pows,zero);    
    }

    for(int i = 0; i < input.size(); i++){
        for(int j = 0; j < input[i].size(); j++){
            delete_gate(input[i][j]);
        }
    }
    for(int i = 0; i < pp.size(); i++){
        delete_gate(pp[i]);
    }
    for(int i = 0; i < range_table.size(); i++){
        delete_gate(range_table[i]);
    }
    for(int i = 0; i < left_rotations.size(); i++){
        delete_gate(left_rotations[i]);
    }
    for(int i = 0; i < right_rotations.size(); i++){
        delete_gate(right_rotations[i]);
    }
    for(int i  =0; i < left_shift_pows.size(); i++){
        delete_gate(left_shift_pows[i]);
        delete_gate(right_shift_pows[i]);
    }
    for(int i = 0; i < shifts.size(); i++){
        delete_gate(shifts[i]);
    }
    for(int i = 0; i < 4; i++){
        delete_gate(pows[i]);
    }
    delete_gate(zero);

    tr_tuple t;
    t.type = 255;
    t.idx_o = -1;
    t.value_o = -1;
    labels = 1;
    tr[ct] = t;
    // write in buffer
    ct = 0;
    mtx2.unlock();
    mtx.lock();   
}

gt lookup_box(gt &i, gt &zero, int idx){
    gt num;
    if(i.value.real >= 256){
        printf("LError %d\n",i.value.real);
        exit(-1);
    }
    init_gate(num,F(lookup_table[idx][i.value.real]));
    if(lookup_table[idx][i.value.real] >= 256){
        printf(">> Error %d\n",lookup_table[idx][i.value.real]);
    }
    tr[ct].type = idx+3;
    tr[ct].idx_o = num.idx;
    tr[ct].value_o = num.value;
    tr[ct].idx_l = i.idx;
    tr[ct].value_l = i.value; 
    tr[ct].idx_r = zero.idx;
    tr[ct].value_r = zero.value;
    tr[ct].access_r = zero.access;
    zero.access++;
    tr[ct].access_l = i.access;
    i.access++;
    tr[ct].access_o = 0;
    num.access = 1;
    ct++;
    if(BUFFER_SPACE_tr == ct){
            ct = 0;
            // semaphore down
            mtx2.unlock();
            mtx.lock();
        }

    return num;
}

void encrypt(vector<gt> &element, vector<vector<gt>> &key, gt &zero){
    
    vector<gt> out(element.size());
    for(int i = 0; i < element.size(); i++){
        out[i] = xor_gate(element[i],key[0][i],1);
    }
    for(int i = 1; i < 9; i++){
        vector<gt> temp1(element.size());
        for(int j = 0; j < temp1.size(); j++){
            temp1[j] = lookup_box(out[j],zero,2);
        }
        vector<vector<gt>> temp2(element.size());
        for(int j = 0; j < temp2.size(); j++){
            temp2[j].resize(3);
            temp2[j][1] = lookup_box(temp1[j],zero,3);
            temp2[j][2] = lookup_box(temp1[j],zero,4);
            temp2[j][0] = temp1[j];
        }
        vector<gt> temp3(element.size());
        for(int k = 0; k < 4; k++){
            gt xor1 = xor_gate(temp2[4*k][1],temp2[4*k+1][2],1);
            gt xor2 = xor_gate(temp2[4*k+2][0],temp2[4*k+3][0],1);
            temp3[4*k] = xor_gate(xor1,xor2,1);               
            delete_gate(xor1);delete_gate(xor2);
            xor1 = xor_gate(temp2[4*k][0],temp2[4*k+1][1],1);
            xor2 = xor_gate(temp2[4*k+2][2],temp2[4*k+3][0],1);
            temp3[4*k+1] = xor_gate(xor1,xor2,1);               
            delete_gate(xor1);delete_gate(xor2);
            xor1 = xor_gate(temp2[4*k][0],temp2[4*k+1][0],1);
            xor2 = xor_gate(temp2[4*k+2][1],temp2[4*k+3][2],1);
            temp3[4*k+2] = xor_gate(xor1,xor2,1);               
            delete_gate(xor1);delete_gate(xor2);
            xor1 = xor_gate(temp2[4*k][2],temp2[4*k+1][0],1);
            xor2 = xor_gate(temp2[4*k+2][0],temp2[4*k+3][1],1);
            temp3[4*k+3] = xor_gate(xor1,xor2,1);               
            delete_gate(xor1);delete_gate(xor2);
        }
        
        
        for(int j  =0 ; j < temp2.size(); j++){
            for(int k = 0; k < temp2[j].size(); k++){
                delete_gate(temp2[j][k]);
            }
        }   
        vector<gt> temp(out.size());
        for(int k = 0; k < temp.size(); k++){
            temp[k] = xor_gate(temp3[k],key[i][k],1);
        }
        for(int j = 0; j < temp3.size(); j++){
            delete_gate(temp3[j]);
        }
        for(int j = 0; j < temp3.size(); j++){
            delete_gate(out[j]);
            out[j] = temp[j];
        }        
    }
    
    for(int j = 0; j < out.size(); j++){
        delete_gate(out[j]);
    }
}


void AES(vector<vector<gt>> &input, vector<vector<gt>> &keys){
    gt zero;
    init_gate(zero,F(0));
    for(int i = 0; i < input.size(); i++){
        encrypt(input[i], keys, zero);
    }

    for(int i = 0; i < input.size(); i++){
        for(int j = 0; j < input[i].size(); j++){
            delete_gate(input[i][j]);
        }
    }
    for(int i = 0; i < keys.size(); i++){
        for(int j = 0; j < keys[i].size(); j++){
            delete_gate(keys[i][j]);
        }
    }
    delete_gate(zero);
    tr_tuple t;
    t.type = 255;
    t.idx_o = -1;
    t.value_o = -1;
    labels = 1;
    tr[ct] = t;
    // write in buffer
    ct = 0;
    mtx2.unlock();
    mtx.lock();   

}

void range_query(vector<gt> &DB, gt &L, gt &R){
    vector<gt> range_table(256);
    vector<gt> pows(domain/8);
    gt zero,minus_one;

    for(int i = 0; i < 256; i++){
        init_gate(range_table[i],F(i));
    }
    for(int i = 0; i < pows.size(); i++){
        init_gate(pows[i],F(1ULL<<(8*i)));
    }
    init_gate(zero,F(0));
    init_gate(minus_one,F(-1));

    vector<gt> Lbytes = get_bytes(L,range_table,pows,zero),Rbytes = get_bytes(L,range_table,pows,zero);
    vector<gt> max(Lbytes.size());
    for(int i = 0; i < DB.size(); i++){
        vector<gt> bytes = get_bytes(DB[i],range_table,pows,zero);
        gt bit1 = ltu_gate(bytes,Rbytes,1);
        gt bit2 = ltu_gate(Lbytes,bytes,1);
        gt bit = mul_gate(bit1,bit2);
        delete_gate(bit1);
        delete_gate(bit2);
        vector<gt> temp_max(bytes.size());
        for(int j = 0; j < temp_max.size(); j++){
            temp_max[j] = mul_gate(bytes[j],bit);
        }
        delete_gate(bit);
        
        for(int j = 0; j < bytes.size(); j++){
            delete_gate(bytes[j]);
        }
        if(i == 0){
            for(int j = 0; j  < temp_max.size(); j++){
                max[j] = temp_max[j];
            }
        }else{
            gt max_bit = ltu_gate(temp_max,max,1);
            gt max_bit_neg = add_gate(max_bit,minus_one);
            for(int j = 0; j < max.size(); j++){
                gt temp_prod1 = mul_gate(max[j],max_bit);
                gt temp_prod2 = mul_gate(temp_max[j],max_bit_neg);
                delete_gate(max[j]);
                delete_gate(temp_max[j]);
                max[j] = add_gate(temp_prod1,temp_prod2);        
                delete_gate(temp_prod1);
                delete_gate(temp_prod2);        
            }            
            delete_gate(max_bit);
            delete_gate(max_bit_neg);
        }
    }
    for(int i = 0; i < max.size(); i++){
        delete_gate(max[i]);
    }
    delete_gate(zero);
    for(int i = 0; i < pows.size(); i++){
        delete_gate(pows[i]);
    }
    for(int i = 0; i < 256; i++){
        delete_gate(range_table[i]);
    }
    for(int i = 0; i < Lbytes.size(); i++){
        delete_gate(Lbytes[i]);
        delete_gate(Rbytes[i]);
    }
    for(int i = 0; i < DB.size(); i++){
        delete_gate(DB[i]);
    }
    delete_gate(R);
    delete_gate(L);
    delete_gate(minus_one);
    tr_tuple t;
    t.type = 255;
    t.idx_o = -1;
    t.value_o = -1;
    labels = 1;
    tr[ct] = t;
    // write in buffer
    ct = 0;
    mtx2.unlock();
    mtx.lock();   

}

void inference(vector<gt> &input, vector<vector<vector<gt>>> &weights, vector<vector<vector<unsigned short>>> &indexes){
    vector<gt> hidden_layer(1024);
    gt zero;init_gate(zero,F(0));
    for(int i = 0; i < indexes[0].size(); i++){
        for(int j = 0; j < indexes[0][i].size(); j++){
            if(j == 0){
                hidden_layer[i] = mul_gate(weights[0][i][j],input[indexes[0][i][j]]);
            }else{
                gt temp = mul_gate(weights[0][i][j],input[indexes[0][i][j]]);
                gt temp_sum = add_gate(hidden_layer[i],temp);
                delete_gate(temp);
                delete_gate(hidden_layer[i]);
                hidden_layer[i] = temp_sum;
            }
        }
        if(indexes[0][i].size() == 0){
            hidden_layer[i] = zero;
        }
    }
    vector<gt> output_layer(128);
    for(int i = 0; i < indexes[1].size(); i++){
        for(int j = 0; j < indexes[1][i].size(); j++){
            if(j == 0){
                output_layer[i] = mul_gate(weights[1][i][j],hidden_layer[indexes[1][i][j]]);
            }else{
                gt temp = mul_gate(weights[1][i][j],hidden_layer[indexes[1][i][j]]);
                gt temp_sum = add_gate(output_layer[i],temp);
                delete_gate(temp);
                delete_gate(output_layer[i]);
                output_layer[i] = temp_sum;
            }
        }
        if(indexes[1][i].size() == 0){
            output_layer[i] = zero;
        }
    }

    for(int i = 0; i < weights.size(); i++){
        for(int j = 0; j < weights[i].size(); j++){
            for(int k = 0; k < weights[i][j].size(); k++){
                delete_gate(weights[i][j][k]);
            }
        }
    }
    for(int i = 0; i < input.size(); i++){
        delete_gate(input[i]);
    }
    for(int i = 0; i < hidden_layer.size(); i++){
        delete_gate(hidden_layer[i]);
    }
    for(int i = 0; i < output_layer.size(); i++){
        delete_gate(output_layer[i]);
    }
    delete_gate(zero);

    tr_tuple t;
    t.type = 255;
    t.idx_o = -1;
    t.value_o = -1;
    labels = 1;
    tr[ct] = t;
    // write in buffer
    ct = 0;
    mtx2.unlock();
    mtx.lock();   

}   

void MLP_inference(vector<gt> &input, vector<vector<vector<gt>>> &weights){
    gt zero;init_gate(zero,F(0));
    vector<gt> inp = input;
    for(int i = 0; i < weights.size(); i++){
        vector<gt> hidden_layer(weights[i].size());
        for(int j = 0; j < weights[i].size(); j++){
            for(int k = 0; k < weights[i][0].size(); k++){
                if(k == 0){
                    hidden_layer[j] = mul_gate(weights[i][j][k],inp[k]);
                }else{
                    gt temp = mul_gate(weights[i][j][k],inp[k]);
                    gt temp_sum = add_gate(hidden_layer[j],temp);
                    delete_gate(temp);
                    delete_gate(hidden_layer[j]);
                    hidden_layer[j] = temp_sum;    
                }
            }
        }
        for(int j = 0; j < inp.size(); j++){
            delete_gate(inp[j]);
        }
        inp = hidden_layer;
    }
    for(int i = 0; i < weights.size(); i++){
        for(int j = 0; j < weights[i].size(); j++){
            for(int k = 0; k < weights[i][j].size(); k++){
                delete_gate(weights[i][j][k]);
            }
        }
    }
    for(int j = 0; j < inp.size(); j++){
        delete_gate(inp[j]);
    }
       
    delete_gate(zero);

    tr_tuple t;
    t.type = 255;
    t.idx_o = -1;
    t.value_o = -1;
    labels = 1;
    tr[ct] = t;
    // write in buffer
    ct = 0;
    mtx2.unlock();
    mtx.lock();   

}


void Seval_Oracle(){
    // arbitrary arithmetic circuit
    if(fun == 1){
        mtx.lock();
        while(true){
            vector<gt> input(input_size);
            for(int i = 0; i < input.size(); i++){
                init_gate(input[i],F(3221*i+1));
            }
            fun1(input);
            //printf("==== Reset ====\n");
        }
    }// range proofs
    else if(fun == 2){
        mtx.lock();
        lookup_table.resize(1);
        lookup_table[0].resize(1ULL<<16);
        for(int i = 0; i < (1<<16); i++){
            lookup_table[0][i] = i;
        }
        while(true){
            vector<gt> pows(2),input(input_size);
            init_gate(pows[0],F(1));
            init_gate(pows[1],F(1<<16));
            for(int i = 0; i < input_size; i++){
                init_gate(input[i],F(i+31)); 
            }
            range_proof(pows,input);
        }
    }else if(fun == 3){
        mtx.lock();
        while(true){
            vector<gt> pows(32),input(input_size);
            
            for(int i = 0; i < pows.size(); i++){
                init_gate(pows[i],F(1ULL<<i));
            }
            for(int i = 0; i < input_size; i++){
                init_gate(input[i],F(i+31)); 
            }
            range_proof_naive(pows,input);
        }
    }else if(fun == 4){
        lookup_table.resize(10);
        lookup_table[0].resize(1ULL<<16);
        for(int i = 0; i < (1<<16); i++){
            lookup_table[0][i] = i;
        }
        create_xor_table(1);
        create_Lshift_tables(2);
        create_Rshift_tables(2+4);
        mtx.lock();
        while(true){
            vector<gt> pp(64);
            vector<vector<gt>> inputs(input_size);
            for(int i = 0; i < input_size; i++){
                inputs[i].resize(16);
                for(int j = 0; j < inputs[i].size(); j++){
                    init_gate(inputs[i][j],F(i*4+j));
                }
            }
            for(int i  =0; i < pp.size(); i++){
                init_gate(pp[i],F(i));
            }
            vector<gt> left_rotations(10),right_rotations(10);
            vector<gt> shifts(2);
            init_gate(shifts[0],F(11));
            init_gate(shifts[1],F(9));
            for(int i = 0; i < 10; i++){
                init_gate(left_rotations[i],F(i+2));
                init_gate(right_rotations[i],F(32-(i+2)));
            }
            vector<gt> right_shift_pows(4),left_shift_pows(4);
            for(int i = 0; i < 4; i++){
                init_gate(right_shift_pows[i],F(1ULL<<(4*i)));
                init_gate(left_shift_pows[i],F(1ULL<<(4*i)));
            }

            SHA256(inputs,pp,left_rotations,right_rotations,left_shift_pows, right_shift_pows,shifts);
        }
    }else if(fun == 5){
        lookup_table.resize(5);
        lookup_table[0].resize(1ULL<<16);
        for(int i = 0; i < 1ULL<<16; i++){
            lookup_table[0][i] = (i);
        }
        create_xor_table(1);
        create_Sbox(2);
        create_MixBox(3);
        create_MixBox(4);
        mtx.lock();
        while(true){
            vector<vector<gt>> inputs(input_size);
            vector<vector<gt>> keys(10);
            for(int i = 0; i < input_size; i++){
                inputs[i].resize(16);
                for(int j = 0; j < 16; j++){
                    init_gate(inputs[i][j],F((i*122+j)%256));
                } 
            }
            for(int i = 0; i < keys.size(); i++){
                keys[i].resize(16);
                for(int j = 0; j < 16; j++){
                    init_gate(keys[i][j],F((i+j+1)%256));
                }
            }
            AES(inputs,keys);

        }
    }else if(fun == 6){
        lookup_table.resize(5);
        lookup_table[0].resize(1ULL<<16);
        for(int i = 0; i < 1ULL<<16; i++){
            lookup_table[0][i] = (i);
        }
        create_ltu_table(1);
        create_eq_table(2);
        mtx.lock();
        while(true){
            vector<gt> DB(input_size);
            for(int i = 0; i < input_size; i++){
                init_gate(DB[i],F((i+12)%domain));                 
            }
            gt L,R;
            init_gate(R,F(321));
            init_gate(L,F(21));
            
            range_query(DB,L,R);
        }                
    }else if(fun == 7){
        mtx.lock();
        while(true){
            gt x;
            init_gate(x,F(1));
            dummy_comp(x);
        }
    }else if(fun == 8){
        mtx.lock();
        int model_size = (int)(prune_rate*1081344);
        vector<gt> input(128*128);
        vector<vector<vector<gt>>> weights(2);
        vector<vector<vector<unsigned short>>> indexes(2);
        indexes[0].resize(1024);
        weights[0].resize(1024);
        indexes[1].resize(128);
        weights[1].resize(128);
        for(int i = 0; i <  (int)(prune_rate*1024*128*128); i++){
            indexes[0][((unsigned int)rand())%1024].push_back(((unsigned int)rand())%(128*128));
        }
        for(int i = 0; i <  (int)(prune_rate*1024*128); i++){
            indexes[1][((unsigned int)rand())%128].push_back(((unsigned int)rand())%(256));
        }
        for(int i = 0; i < indexes[0].size(); i++){
            weights[0][i].resize(indexes[0][i].size());
        }
        for(int i = 0; i < indexes[1].size(); i++){
            weights[1][i].resize(indexes[1][i].size());
        }
        while(true){
            for(int i = 0; i < input.size(); i++){
                init_gate(input[i],F((i+1)%256));
            }
            for(int i = 0; i < weights[0].size(); i++){
                for(int j = 0; j < weights[0][i].size(); j++){
                    init_gate(weights[0][i][j],F((j+i)%256));
                }
            }
            for(int i = 0; i < weights[1].size(); i++){
                for(int j = 0; j < weights[1][i].size(); j++){
                    init_gate(weights[1][i][j],F((j+i)%256));
                }
            }
            inference(input,weights,indexes);
        }
    }else if(fun == 9){

        mtx.lock();
        vector<gt> input(layer_size[0]);
        vector<vector<vector<gt>>> weights(layer_size.size()-1);
        int msize = 0;
        for(int i = 0; i < weights.size(); i++){
            weights[i].resize(layer_size[i+1]);
            for(int j = 0; j < weights[i].size(); j++){
                weights[i][j].resize(layer_size[i]);
            }
            msize += weights[i].size()*weights[i][0].size();
        }
        printf("Model size : %d\n",msize);
        
        while(true){
            for(int i = 0; i < weights.size(); i++){
                for(int j = 0; j < weights[i].size(); j++){
                    for(int k = 0; k < weights[i][j].size(); k++){
                        init_gate(weights[i][j][k],F((j+i + k)%256));                        
                    }
                }
            }
            for(int i = 0; i < input.size(); i++){
                init_gate(input[i],F((i+1)%256));
            }
            MLP_inference(input,weights);
        }
        
    }
}

