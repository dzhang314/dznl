import { readFileSync } from "fs";

const dznl = await WebAssembly.instantiate(readFileSync("dznl.wasm"));

const offset = 0;
const num_points = 3;
const dimension = 3;
const length = num_points * dimension;

const array = new Float64Array(
    dznl.instance.exports.memory.buffer,
    offset,
    length
);

dznl.instance.exports.random_fill_sphere_f64(
    array.byteOffset,
    num_points,
    BigInt("0")
);

console.log(array.join(", "));
