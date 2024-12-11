#!/bin/sh

set -euxo pipefail

for f in dznl/*.hpp; do
    include-what-you-use -I dznl -DDZNL_REQUEST_F16 $f
done

compile_and_run_gcc() {
    /opt/homebrew/bin/g++-14 -std=c++17 \
        -O3 -march=native \
        -Wall -Wextra -pedantic -Werror \
        -isystem /opt/homebrew/include -I . \
        "$1" -o "$2"
    "$2"
}

compile_and_run_clang() {
    /opt/homebrew/opt/llvm/bin/clang++ -std=c++17 \
        -O3 -march=native \
        -Weverything -Werror \
        -Wno-padded \
        -Wno-float-equal \
        -Wno-c++98-compat \
        -Wno-c++98-compat-pedantic \
        -isystem /opt/homebrew/include -I . \
        "$1" -o "$2"
    "$2"
}

compile_and_run_apple_clang() {
    clang++ -std=c++17 \
        -O3 -march=native \
        -Weverything -Werror \
        -Wno-padded \
        -Wno-float-equal \
        -Wno-c++98-compat \
        -Wno-c++98-compat-pedantic \
        -Wno-poison-system-directories \
        -isystem /opt/homebrew/include -I . \
        "$1" -o "$2"
    "$2"
}

compile_and_run_gcc test/TestArithmetic.cpp bin/TestArithmeticGCC
compile_and_run_clang test/TestArithmetic.cpp bin/TestArithmeticClang
compile_and_run_apple_clang test/TestArithmetic.cpp bin/TestArithmeticAppleClang

compile_and_run_gcc test/TestFloatingPoint.cpp bin/TestFloatingPointGCC
compile_and_run_clang test/TestFloatingPoint.cpp bin/TestFloatingPointClang
compile_and_run_apple_clang test/TestFloatingPoint.cpp bin/TestFloatingPointAppleClang
