set -e

NATIVE_FLAGS=(
    -march=native
)

WASM_FLAGS=(
    --target=wasm32
    -mmultivalue
    -Xclang=-target-abi
    -Xclang=experimental-mv
)

WARNING_FLAGS=(
    -Weverything
    -Wno-c++98-compat
    -Wno-float-equal
)

clang++ -std=c++20 ${NATIVE_FLAGS[*]} ${WARNING_FLAGS[*]} -O3 \
    -nostdlib -Icpp -c native_interface.cpp -o dznl.o

objdump -M intel -d --no-show-raw-insn dznl.o

clang++ -std=c++20 ${WASM_FLAGS[*]} ${WARNING_FLAGS[*]} -O3 \
    -nostdlib -Icpp -c wasm_interface.cpp -o dznl.wasm

wasm2wat dznl.wasm
