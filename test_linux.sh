#!/bin/sh

set -eu

for f in dznl/*.hpp; do
    include-what-you-use -I dznl $f
done

compile_and_run_gcc_11() {
    echo "Compiling $1 -> $2 with GCC 11"
    g++-11 -std=c++17 \
        -Wall -Wextra -pedantic -Werror -fmax-errors=1 \
        -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_gcc_12() {
    echo "Compiling $1 -> $2 with GCC 12"
    g++-12 -std=c++17 \
        -Wall -Wextra -pedantic -Werror -fmax-errors=1 \
        -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_gcc_13() {
    echo "Compiling $1 -> $2 with GCC 13"
    g++-13 -std=c++17 \
        -Wall -Wextra -pedantic -Werror -fmax-errors=1 \
        -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_gcc_14() {
    echo "Compiling $1 -> $2 with GCC 14"
    g++-14 -std=c++17 \
        -Wall -Wextra -pedantic -Werror -fmax-errors=1 \
        -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_clang_14() {
    echo "Compiling $1 -> $2 with Clang 14"
    clang++-14 -std=c++17 \
        -Weverything -Werror -ferror-limit=1 \
        -Wno-padded \
        -Wno-float-equal \
        -Wno-c++98-compat \
        -Wno-c++98-compat-pedantic \
        -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_clang_15() {
    echo "Compiling $1 -> $2 with Clang 15"
    clang++-15 -std=c++17 \
        -Weverything -Werror -ferror-limit=1 \
        -Wno-padded \
        -Wno-float-equal \
        -Wno-c++98-compat \
        -Wno-c++98-compat-pedantic \
        -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_clang_16() {
    echo "Compiling $1 -> $2 with Clang 16"
    clang++-16 -std=c++17 \
        -Weverything -Werror -ferror-limit=1 \
        -Wno-padded \
        -Wno-float-equal \
        -Wno-c++98-compat \
        -Wno-c++98-compat-pedantic \
        -Wno-unsafe-buffer-usage \
        -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_clang_17() {
    echo "Compiling $1 -> $2 with Clang 17"
    clang++-17 -std=c++17 \
        -Weverything -Werror -ferror-limit=1 \
        -Wno-padded \
        -Wno-float-equal \
        -Wno-c++98-compat \
        -Wno-c++98-compat-pedantic \
        -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_clang_18() {
    echo "Compiling $1 -> $2 with Clang 18"
    clang++-18 -std=c++17 \
        -Weverything -Werror -ferror-limit=1 \
        -Wno-padded \
        -Wno-float-equal \
        -Wno-c++98-compat \
        -Wno-c++98-compat-pedantic \
        -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_icpx() {
    echo "Compiling $1 -> $2 with ICPX"
    /opt/intel/oneapi/compiler/latest/bin/icpx -std=c++17 \
        -Wall \
        -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_nvcpp() {
    echo "Compiling $1 -> $2 with NVC++"
    /opt/nvidia/hpc_sdk/Linux_x86_64/2024/compilers/bin/nvc++ -std=c++17 \
        -Wall \
        -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

mkdir -p bin

compile_and_run_gcc_11 test/TestArithmetic.cpp bin/TestArithmeticGCC11 &
compile_and_run_gcc_12 test/TestArithmetic.cpp bin/TestArithmeticGCC12 &
compile_and_run_gcc_13 test/TestArithmetic.cpp bin/TestArithmeticGCC13 &
compile_and_run_gcc_14 test/TestArithmetic.cpp bin/TestArithmeticGCC14 &
compile_and_run_clang_14 test/TestArithmetic.cpp bin/TestArithmeticClang14 &
compile_and_run_clang_15 test/TestArithmetic.cpp bin/TestArithmeticClang15 &
compile_and_run_clang_16 test/TestArithmetic.cpp bin/TestArithmeticClang16 &
compile_and_run_clang_17 test/TestArithmetic.cpp bin/TestArithmeticClang17 &
compile_and_run_clang_18 test/TestArithmetic.cpp bin/TestArithmeticClang18 &
compile_and_run_icpx test/TestArithmetic.cpp bin/TestArithmeticICPX &
compile_and_run_nvcpp test/TestArithmetic.cpp bin/TestArithmeticNVCPP &

wait

compile_and_run_gcc_11 test/TestFloatingPoint.cpp bin/TestFloatingPointGCC11 &
compile_and_run_gcc_12 test/TestFloatingPoint.cpp bin/TestFloatingPointGCC12 &
compile_and_run_gcc_13 test/TestFloatingPoint.cpp bin/TestFloatingPointGCC13 &
compile_and_run_gcc_14 test/TestFloatingPoint.cpp bin/TestFloatingPointGCC14 &
compile_and_run_clang_14 test/TestFloatingPoint.cpp bin/TestFloatingPointClang14 &
compile_and_run_clang_15 test/TestFloatingPoint.cpp bin/TestFloatingPointClang15 &
compile_and_run_clang_16 test/TestFloatingPoint.cpp bin/TestFloatingPointClang16 &
compile_and_run_clang_17 test/TestFloatingPoint.cpp bin/TestFloatingPointClang17 &
compile_and_run_clang_18 test/TestFloatingPoint.cpp bin/TestFloatingPointClang18 &
compile_and_run_icpx test/TestFloatingPoint.cpp bin/TestFloatingPointICPX &
compile_and_run_nvcpp test/TestFloatingPoint.cpp bin/TestFloatingPointNVCPP &

wait

compile_and_run_gcc_11 test/TestFloatToString.cpp bin/TestFloatToStringGCC11 &
compile_and_run_gcc_12 test/TestFloatToString.cpp bin/TestFloatToStringGCC12 &
compile_and_run_gcc_13 test/TestFloatToString.cpp bin/TestFloatToStringGCC13 &
compile_and_run_gcc_14 test/TestFloatToString.cpp bin/TestFloatToStringGCC14 &
compile_and_run_clang_14 test/TestFloatToString.cpp bin/TestFloatToStringClang14 &
compile_and_run_clang_15 test/TestFloatToString.cpp bin/TestFloatToStringClang15 &
compile_and_run_clang_16 test/TestFloatToString.cpp bin/TestFloatToStringClang16 &
compile_and_run_clang_17 test/TestFloatToString.cpp bin/TestFloatToStringClang17 &
compile_and_run_clang_18 test/TestFloatToString.cpp bin/TestFloatToStringClang18 &
compile_and_run_icpx test/TestFloatToString.cpp bin/TestFloatToStringICPX &
# compile_and_run_nvcpp test/TestFloatToString.cpp bin/TestFloatToStringNVCPP &

wait

compile_and_run_gcc_11 test/TestToHexString.cpp bin/TestToHexStringGCC11 &
compile_and_run_gcc_12 test/TestToHexString.cpp bin/TestToHexStringGCC12 &
compile_and_run_gcc_13 test/TestToHexString.cpp bin/TestToHexStringGCC13 &
compile_and_run_gcc_14 test/TestToHexString.cpp bin/TestToHexStringGCC14 &
compile_and_run_clang_14 test/TestToHexString.cpp bin/TestToHexStringClang14 &
compile_and_run_clang_15 test/TestToHexString.cpp bin/TestToHexStringClang15 &
compile_and_run_clang_16 test/TestToHexString.cpp bin/TestToHexStringClang16 &
compile_and_run_clang_17 test/TestToHexString.cpp bin/TestToHexStringClang17 &
compile_and_run_clang_18 test/TestToHexString.cpp bin/TestToHexStringClang18 &
compile_and_run_icpx test/TestToHexString.cpp bin/TestToHexStringICPX &
compile_and_run_nvcpp test/TestToHexString.cpp bin/TestToHexStringNVCPP &

wait
