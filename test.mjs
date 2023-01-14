import { readFileSync } from "fs";

const dznl = await WebAssembly.instantiate(readFileSync("dznl.wasm"));

const offset = 0;
const length = 16384;
const array = new Float64Array(
    dznl.instance.exports.memory.buffer,
    offset,
    length
);

dznl.instance.exports.random_fill(
    array.byteOffset,
    length,
    BigInt(1)
);

console.log(array.join(", "));
