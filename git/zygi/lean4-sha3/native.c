#include "lean/lean.h"
#include "tiny_sha3/sha3.h"
#include <stdio.h>

lean_obj_res lean_native_sha3_256(b_lean_obj_arg input_byte_array) {
    const size_t input_size_in_bytes = lean_sarray_size(input_byte_array);
    const size_t out_size_in_bytes = 256 / 8;
    const lean_obj_res res = lean_alloc_sarray(1, out_size_in_bytes, out_size_in_bytes);
    sha3(lean_sarray_cptr(input_byte_array), input_size_in_bytes, lean_sarray_cptr(res), out_size_in_bytes);
    return res;
}