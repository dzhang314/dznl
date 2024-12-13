#!/bin/sh

set -eux

for f in dznl/*.hpp; do
    include-what-you-use -I dznl $f
done

compile_and_run_gcc() {
    g++ -std=c++17 \
        -Wall -Wextra -pedantic -Werror \
        -I . \
        "$1" -o "$2"
    "$2"
}

compile_and_run_clang() {
    clang++ -std=c++17 \
        -Weverything -Werror \
        -Wno-padded \
        -Wno-float-equal \
        -Wno-c++98-compat \
        -Wno-c++98-compat-pedantic \
        -I . \
        "$1" -o "$2"
    "$2"
}

mkdir -p bin

compile_and_run_gcc test/TestArithmetic.cpp bin/TestArithmeticGCC
compile_and_run_clang test/TestArithmetic.cpp bin/TestArithmeticClang

compile_and_run_gcc test/TestFloatingPoint.cpp bin/TestFloatingPointGCC
compile_and_run_clang test/TestFloatingPoint.cpp bin/TestFloatingPointClang

compile_and_run_gcc test/TestFloatToString.cpp bin/TestFloatToStringGCC
compile_and_run_clang test/TestFloatToString.cpp bin/TestFloatToStringClang
