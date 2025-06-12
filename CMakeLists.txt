cmake_minimum_required(VERSION 3.10)
project(ProofOfLearning)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_FLAGS "-w -march=native  -mavx -lgmp -msha")
set(CMAKE_C_FLAGS "-w -march=native -mavx -lgmp -msha")



link_directories(lib)
link_directories(Blake)

include_directories(src)
include_directories(lib)
include_directories(Blake)



add_subdirectory(src)
add_subdirectory(Blake)

