aux_source_directory(. SRC)
include_directories(.)
add_executable(pigeon ${SRC})

target_link_libraries(pigeon gmp pthread XKCP blake3)
