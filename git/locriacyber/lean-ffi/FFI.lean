-- enum ffi_abi
inductive ffi_abi where
| mk : UInt8 -> ffi_abi
deriving Inhabited

-- ffi_type *
inductive ffi_type_Pointer where
| mk : USize -> ffi_type_Pointer
deriving Inhabited
-- TODO: auto release memory for this type
-- some ffi_type are static memory though

-- ffi_cif *
inductive ffi_cif_Pointer where
| mk : USize -> ffi_cif_Pointer
deriving Inhabited
-- TODO: auto release memory for this type

-- void (*) (void)
inductive FunctionPointer where
| mk : USize -> FunctionPointer
deriving Inhabited

inductive Error_prep_cif where
| BAD_TYPE_DEF
| BAD_ABI

attribute [export lean_Error_prep_cif_BAD_TYPE_DEF] Error_prep_cif.BAD_TYPE_DEF
attribute [export lean_Error_prep_cif_BAD_ABI] Error_prep_cif.BAD_ABI



@[extern "LEAN_FFI_DEFAULT_ABI"]
opaque FFI_DEFAULT_ABI : ffi_abi


inductive FFIType where
| uint
| uint32
| void

def CUInt : Type := UInt32

def getLeanType : FFIType -> Type
| .uint32 => UInt32
| .uint => CUInt
| .void => Unit

@[extern "lean_ffi_prep_cif"]
opaque ffi_prep_cif (abi : ffi_abi) (rtype : @& ffi_type_Pointer) (atypes : @& Array ffi_type_Pointer) : EIO Error_prep_cif ffi_cif_Pointer

@[extern "lean_ffi_call"]
opaque ffi_call (cif : @& ffi_cif_Pointer) (fn : FunctionPointer) (rtype : FFIType) (avalues : @& Array AnyPointer) : EIO Unit (getLeanType rtype)
