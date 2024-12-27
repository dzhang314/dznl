#!/bin/sh

set -euo pipefail

for f in dznl/*.hpp; do
    include-what-you-use -I dznl $f
done

compile_and_run_gcc_13() {
    echo "Compiling $1 -> $2 with GCC 13"
    /opt/homebrew/bin/g++-13 -std=c++17 \
        -Wall -Wextra -pedantic -Werror -fmax-errors=1 \
        -isystem /opt/homebrew/include -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_gcc_14() {
    echo "Compiling $1 -> $2 with GCC 14"
    /opt/homebrew/bin/g++-14 -std=c++17 \
        -Wall -Wextra -pedantic -Werror -fmax-errors=1 \
        -isystem /opt/homebrew/include -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_clang_17() {
    echo "Compiling $1 -> $2 with Clang 17"
    /opt/homebrew/opt/llvm@17/bin/clang++ -std=c++17 \
        -Weverything -Werror -ferror-limit=1 \
        -Wno-padded \
        -Wno-float-equal \
        -Wno-c++98-compat \
        -Wno-c++98-compat-pedantic \
        -isystem /opt/homebrew/include -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_clang_18() {
    echo "Compiling $1 -> $2 with Clang 18"
    /opt/homebrew/opt/llvm@18/bin/clang++ -std=c++17 \
        -Weverything -Werror -ferror-limit=1 \
        -Wno-padded \
        -Wno-float-equal \
        -Wno-c++98-compat \
        -Wno-c++98-compat-pedantic \
        -isystem /opt/homebrew/include -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_clang_19() {
    echo "Compiling $1 -> $2 with Clang 19"
    /opt/homebrew/opt/llvm@19/bin/clang++ -std=c++17 \
        -Weverything -Werror -ferror-limit=1 \
        -Wno-padded \
        -Wno-float-equal \
        -Wno-c++98-compat \
        -Wno-c++98-compat-pedantic \
        -isystem /opt/homebrew/include -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

compile_and_run_apple_clang() {
    echo "Compiling $1 -> $2 with Apple Clang"
    clang++ -std=c++17 \
        -Weverything -Werror -ferror-limit=1 \
        -Wno-padded \
        -Wno-float-equal \
        -Wno-c++98-compat \
        -Wno-c++98-compat-pedantic \
        -Wno-poison-system-directories \
        -isystem /opt/homebrew/include -I . \
        "$1" -o "$2"
    "$2"
    echo "$2: $?"
}

mkdir -p bin

compile_and_run_gcc_13 test/TestArithmetic.cpp bin/TestArithmeticGCC13 &
compile_and_run_gcc_14 test/TestArithmetic.cpp bin/TestArithmeticGCC14 &
compile_and_run_clang_17 test/TestArithmetic.cpp bin/TestArithmeticClang17 &
compile_and_run_clang_18 test/TestArithmetic.cpp bin/TestArithmeticClang18 &
compile_and_run_clang_19 test/TestArithmetic.cpp bin/TestArithmeticClang19 &
compile_and_run_apple_clang test/TestArithmetic.cpp bin/TestArithmeticAppleClang &

wait

compile_and_run_gcc_13 test/TestFloatingPoint.cpp bin/TestFloatingPointGCC13 &
compile_and_run_gcc_14 test/TestFloatingPoint.cpp bin/TestFloatingPointGCC14 &
compile_and_run_clang_17 test/TestFloatingPoint.cpp bin/TestFloatingPointClang17 &
compile_and_run_clang_18 test/TestFloatingPoint.cpp bin/TestFloatingPointClang18 &
compile_and_run_clang_19 test/TestFloatingPoint.cpp bin/TestFloatingPointClang19 &
compile_and_run_apple_clang test/TestFloatingPoint.cpp bin/TestFloatingPointAppleClang &

wait

compile_and_run_gcc_13 test/TestFloatToString.cpp bin/TestFloatToStringGCC13 &
compile_and_run_gcc_14 test/TestFloatToString.cpp bin/TestFloatToStringGCC14 &
compile_and_run_clang_17 test/TestFloatToString.cpp bin/TestFloatToStringClang17 &
compile_and_run_clang_18 test/TestFloatToString.cpp bin/TestFloatToStringClang18 &
compile_and_run_clang_19 test/TestFloatToString.cpp bin/TestFloatToStringClang19 &
compile_and_run_apple_clang test/TestFloatToString.cpp bin/TestFloatToStringAppleClang &

wait

compile_and_run_gcc_13 test/TestToHexString.cpp bin/TestToHexStringGCC13 &
compile_and_run_gcc_14 test/TestToHexString.cpp bin/TestToHexStringGCC14 &
compile_and_run_clang_17 test/TestToHexString.cpp bin/TestToHexStringClang17 &
compile_and_run_clang_18 test/TestToHexString.cpp bin/TestToHexStringClang18 &
compile_and_run_clang_19 test/TestToHexString.cpp bin/TestToHexStringClang19 &
compile_and_run_apple_clang test/TestToHexString.cpp bin/TestToHexStringAppleClang &

wait
