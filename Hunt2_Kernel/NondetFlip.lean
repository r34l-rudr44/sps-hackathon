@[noinline] def someList : List Nat := [1, 2, 3]

-- XOR all 64 bits of the address into 1 bit (popcount parity).
def xorAll (a : USize) : USize := Id.run do
  let mut acc : USize := 0
  for i in [0:64] do
    acc := acc ^^^ ((a >>> i.toUSize) &&& 1)
  return acc

unsafe def aslrBitImpl (_ : Unit) : Bool :=
  xorAll (ptrAddrUnsafe someList) == 1

@[implemented_by aslrBitImpl]
def aslrBit (_ : Unit) : Bool := false

#eval (ptrAddrUnsafe someList, xorAll (ptrAddrUnsafe someList), aslrBit ())
theorem maybeProof : aslrBit () = true := by native_decide
#print axioms maybeProof
