set -e

NATIVE_FLAGS=(
    -march=native
    -c
)

WASM_FLAGS=(
    --target=wasm32
    -mmultivalue
    -Xclang=-target-abi
    -Xclang=experimental-mv
    -Wl,--no-entry
)

WARNING_FLAGS=(
    -Weverything
    -Wno-c++98-compat
    -Wno-c++98-compat-pedantic
    -Wno-float-equal
)

clang++ -std=c++20 ${NATIVE_FLAGS[*]} ${WARNING_FLAGS[*]} -O3 \
    -nostdlib -Icpp native_interface.cpp -o dznl.o

objdump -M intel -d --no-show-raw-insn dznl.o

clang++ -std=c++20 ${WASM_FLAGS[*]} ${WARNING_FLAGS[*]} -O3 \
    -nostdlib -Icpp wasm_interface.cpp -o dznl.wasm

wasm2wat dznl.wasm
