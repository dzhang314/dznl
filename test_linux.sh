#!/bin/sh

set -eux

for f in dznl/*.hpp; do
    include-what-you-use -I dznl $f
done

compile_and_run_gcc_11() {
    g++-11 -std=c++17 \
        -Wall -Wextra -pedantic -Werror -fmax-errors=1 \
        -I . \
        "$1" -o "$2"
    "$2"
}

compile_and_run_gcc_12() {
    g++-12 -std=c++17 \
        -Wall -Wextra -pedantic -Werror -fmax-errors=1 \
        -I . \
        "$1" -o "$2"
    "$2"
}

compile_and_run_gcc_13() {
    g++-13 -std=c++17 \
        -Wall -Wextra -pedantic -Werror -fmax-errors=1 \
        -I . \
        "$1" -o "$2"
    "$2"
}

compile_and_run_gcc_14() {
    g++-14 -std=c++17 \
        -Wall -Wextra -pedantic -Werror -fmax-errors=1 \
        -I . \
        "$1" -o "$2"
    "$2"
}

compile_and_run_clang_18() {
    clang++-18 -std=c++17 \
        -Weverything -Werror -ferror-limit=1 \
        -Wno-padded \
        -Wno-float-equal \
        -Wno-c++98-compat \
        -Wno-c++98-compat-pedantic \
        -I . \
        "$1" -o "$2"
    "$2"
}

mkdir -p bin

compile_and_run_gcc_11 test/TestArithmetic.cpp bin/TestArithmeticGCC11 &
compile_and_run_gcc_12 test/TestArithmetic.cpp bin/TestArithmeticGCC12 &
compile_and_run_gcc_13 test/TestArithmetic.cpp bin/TestArithmeticGCC13 &
compile_and_run_gcc_14 test/TestArithmetic.cpp bin/TestArithmeticGCC14 &
compile_and_run_clang_18 test/TestArithmetic.cpp bin/TestArithmeticClang18 &

wait

compile_and_run_gcc_11 test/TestFloatingPoint.cpp bin/TestFloatingPointGCC11 &
compile_and_run_gcc_12 test/TestFloatingPoint.cpp bin/TestFloatingPointGCC12 &
compile_and_run_gcc_13 test/TestFloatingPoint.cpp bin/TestFloatingPointGCC13 &
compile_and_run_gcc_14 test/TestFloatingPoint.cpp bin/TestFloatingPointGCC14 &
compile_and_run_clang_18 test/TestFloatingPoint.cpp bin/TestFloatingPointClang18 &

wait

compile_and_run_gcc_11 test/TestFloatToString.cpp bin/TestFloatToStringGCC11 &
compile_and_run_gcc_12 test/TestFloatToString.cpp bin/TestFloatToStringGCC12 &
compile_and_run_gcc_13 test/TestFloatToString.cpp bin/TestFloatToStringGCC13 &
compile_and_run_gcc_14 test/TestFloatToString.cpp bin/TestFloatToStringGCC14 &
compile_and_run_clang_18 test/TestFloatToString.cpp bin/TestFloatToStringClang18 &

wait

compile_and_run_gcc_11 test/TestToHexString.cpp bin/TestToHexStringGCC11 &
compile_and_run_gcc_12 test/TestToHexString.cpp bin/TestToHexStringGCC12 &
compile_and_run_gcc_13 test/TestToHexString.cpp bin/TestToHexStringGCC13 &
compile_and_run_gcc_14 test/TestToHexString.cpp bin/TestToHexStringGCC14 &
compile_and_run_clang_18 test/TestToHexString.cpp bin/TestToHexStringClang18 &

wait
