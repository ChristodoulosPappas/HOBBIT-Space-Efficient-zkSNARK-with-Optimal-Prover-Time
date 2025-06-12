#pragma once
#include "config_pc.hpp"
#include "circuit.h"


struct stream_descriptor{
    int idx = 0,offset = 0;
    int stage = 0;
    bool finished = false;
        
    size_t pos = 0,pos_j = 0;
    size_t data_size,row_size,col_size,size,layer,tree_pos;
    string name;    
    size_t input_pos,input_pos_j,input_data_size,input_size;
    string input_name;
};

typedef struct stream_descriptor stream_descriptor;

void read_layer(int circuit_num, int layer , vector<F> &V);
void read_H( int layer , vector<F> &H_add,vector<F> &H_mul, vector<F> &V, F beta_h1, F beta_h2 );
void read_G( int layer , vector<F> &G_add,vector<F> &G_mul, vector<F> &V, vector<F> &beta_g1,F beta_h1,
 F beta_g2,F beta_h2,F Vr);
 
void read_stream(stream_descriptor &fd, vector<F> &v, int size);
void read_stream_PC(stream_descriptor &fd, F *v, int size);
void reset_stream(stream_descriptor &fp);
void get_transcript(vector<vector<F>> &transcript);
void compute_H( int layer , F *H_add, F *H_mul, F *V, int layer_size);
void compute_G( int layer , F *G_add,F *G_mul, F *V, F *beta_g1,F V_u, int len);
void read_trace(stream_descriptor &fd, vector<F> &buff_L,vector<F> &buff_R,vector<F> &buff_O,
    vector<int> &buff_S);

void read_mul_tree_data(stream_descriptor &fd, vector<vector<F>> &v, int size, int layer, int distance);
void read_mul_tree_layer(stream_descriptor &fd, vector<F> &v, int size, int layer);
void read_memory(stream_descriptor &fd,  vector<F> &buff_addr, vector<F> &buff_v, vector<F> &buff_f);