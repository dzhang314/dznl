#!/bin/sh

set -euxo pipefail

/opt/homebrew/bin/g++-14 -std=c++17 -O3 -march=native \
    -Wall -Wextra -pedantic -Werror \
    -isystem /opt/homebrew/include \
    -I include test/TestArithmetic.cpp \
    -o bin/TestArithmeticGCC

bin/TestArithmeticGCC

/opt/homebrew/opt/llvm/bin/clang++ -std=c++17 -O3 -march=native \
    -Weverything -Werror \
    -Wno-float-equal \
    -Wno-c++98-compat \
    -Wno-c++98-compat-pedantic \
    -isystem /opt/homebrew/include \
    -I include test/TestArithmetic.cpp \
    -o bin/TestArithmeticClang

bin/TestArithmeticClang

clang++ -std=c++17 -O3 -march=native \
    -Weverything -Werror \
    -Wno-float-equal \
    -Wno-c++98-compat \
    -Wno-c++98-compat-pedantic \
    -Wno-poison-system-directories \
    -isystem /opt/homebrew/include \
    -I include test/TestArithmetic.cpp \
    -o bin/TestArithmeticAppleClang

bin/TestArithmeticAppleClang
