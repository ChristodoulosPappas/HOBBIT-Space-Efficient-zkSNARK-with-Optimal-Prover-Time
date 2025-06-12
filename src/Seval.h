#include "config_pc.hpp"


struct tr_tuple{
    F value_o,value_l,value_r;
    int idx_o,idx_l,idx_r;
    int access_o,access_l,access_r;
    uint8_t type;
};

struct gt{
    F value;
    int idx;
    int access = 0;
};
typedef struct gt;
typedef struct tr_tuple;


void Seval_Oracle();
void Seval();
void get_circuit_info(size_t &gates, size_t &ops);