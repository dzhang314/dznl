set -e

clang \
    -std=c++20 -Weverything -Wno-c++98-compat -Wno-c++98-compat-pedantic \
    -Wno-unsafe-buffer-usage -Wno-float-equal -Wno-missing-prototypes \
    --target=wasm32 -mmultivalue -Xclang=-target-abi -Xclang=experimental-mv \
    -nostdlib -Wl,--no-entry \
    -Icpp \
    -O3 wasm_interface.cpp -o dznl.wasm

wasm2wat dznl.wasm
