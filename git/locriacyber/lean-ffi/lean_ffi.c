#include <ffi.h>
#include <stdio.h>

// var-arg version
// ffi_prep_cif_var

int main() {
    ffi_cif cif_puts;
    ffi_abi abi = FFI_DEFAULT_ABI;
    // get function call

    ffi_type rtype = ffi_type_sint;
    ffi_type atype_0 = ffi_type_pointer;
    ffi_type* atypes[1] = {&atype_0};
    ffi_status err = ffi_prep_cif(&cif_puts, abi, 1, &rtype, &atypes[0]);
    if (err != FFI_OK) return 10;

    int rvalue;
    char * avalue_0 = "Hello World";
    void* avalue[1] = {&avalue_0};

    ffi_call(&cif_puts, (void (*) (void))puts, &rvalue, &avalue[0]);
    
    puts(avalue_0);
    return 0;
}