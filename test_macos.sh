#!/bin/sh

set -e

CompilerFlags="-std=c++17 -I/opt/homebrew/Cellar/doctest/2.4.11/include/ -I./"
GccPath="/opt/homebrew/bin/g++-13"
ClangPath="/opt/homebrew/opt/llvm/bin/clang++"
GccWarningFlags="-Wall -Wextra -Wfatal-errors -pedantic -pedantic-errors"
ClangWarningFlags="-Weverything -Wfatal-errors \
-Wno-c++98-compat -Wno-c++98-compat-pedantic \
-Wno-unsafe-buffer-usage -Wno-float-equal -Wno-padded \
-Wno-poison-system-directories"

compile_and_test() {
    test_name="$(basename "$1" .cpp)"
    echo "${test_name}GCC"
    "$GccPath" $CompilerFlags $GccWarningFlags "$1" \
        -o "bin/${test_name}GCC"; "bin/${test_name}GCC" -m
    echo "${test_name}Clang"
    "$ClangPath" $CompilerFlags $ClangWarningFlags "$1" \
        -o "bin/${test_name}Clang"; "bin/${test_name}Clang" -m
    echo "${test_name}GCCMut"
    "$GccPath" $CompilerFlags $GccWarningFlags -DDZNL_REMOVE_CONST "$1" \
        -o "bin/${test_name}GCCMut"; "bin/${test_name}GCCMut" -m
    echo "${test_name}ClangMut"
    "$ClangPath" $CompilerFlags $ClangWarningFlags -DDZNL_REMOVE_CONST "$1" \
        -o "bin/${test_name}ClangMut"; "bin/${test_name}ClangMut" -m
}

rm -rf bin
mkdir -p bin

for file in test/*.cpp; do compile_and_test "$file"; done
