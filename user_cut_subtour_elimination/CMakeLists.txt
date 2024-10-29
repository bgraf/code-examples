cmake_minimum_required(VERSION 3.18)

option(CMAKE_EXPORT_COMPILE_COMMANDS "Export compile command" ON)

project(tsp_bc VERSION 1.0 LANGUAGES CXX)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_EXTENSIONS ON)

set(LEMON_ENABLE_COIN       NO CACHE BOOL "" FORCE)
set(LEMON_ENABLE_GLPK       NO CACHE BOOL "" FORCE)
set(LEMON_ENABLE_ILOG       NO CACHE BOOL "" FORCE)
set(LEMON_ENABLE_SOPLEX     NO CACHE BOOL "" FORCE)
add_subdirectory(../lemon-1.3.1 build_lemon)


add_executable(tsp_bc tsp_bc.cc)
target_include_directories(tsp_bc PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_include_directories(tsp_bc PRIVATE 
    "${CMAKE_CURRENT_LIST_DIR}/../or-tools_x86_64_Ubuntu-24.04_cpp_v9.11.4210/include"
    "${CMAKE_CURRENT_LIST_DIR}/../lemon-1.3.1"
)
target_compile_features(tsp_bc PUBLIC cxx_std_20)
target_link_directories(tsp_bc PRIVATE "${CMAKE_CURRENT_LIST_DIR}/../or-tools_x86_64_Ubuntu-24.04_cpp_v9.11.4210/lib")
target_link_libraries(tsp_bc PRIVATE ortools lemon)
