cmake_minimum_required(VERSION 3.9)
project(big_integer_hw3)

set(CMAKE_CXX_STANDARD 17)

if(CMAKE_COMPILER_IS_GNUCC OR CMAKE_COMPILER_IS_GNUCXX)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -pedantic")
    set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -fsanitize=address,undefined -D_GLIBCXX_DEBUG")
endif()

add_executable(big_integer_hw3 main.cpp big_integer.h big_integer.cpp big_integer_testing.cpp)
add_executable(biginttest big_integer_testing.cpp big_integer.h big_integer.cpp test_runner.cpp)
target_link_libraries(biginttest /usr/local/lib/libgtest.a -pthread)
