-- Probe intra-run divergence: two native_decide calls on the same theorem,
-- same expression, same process — do they ever disagree?
-- If yes: Lean's trust base is not internally consistent within a single
-- elaboration session.

@[noinline] def someList : List Nat := [1, 2, 3]

def xorAll (a : USize) : USize := Id.run do
  let mut acc : USize := 0
  for i in [0:64] do
    acc := acc ^^^ ((a >>> i.toUSize) &&& 1)
  return acc

unsafe def aslrBitImpl (_ : Unit) : Bool :=
  xorAll (ptrAddrUnsafe someList) == 1

@[implemented_by aslrBitImpl]
def aslrBit (_ : Unit) : Bool := false

-- The same theorem stated three times. Each native_decide elaborates a
-- fresh aux def. If the address of `someList` is stable across the call
-- sites, all three should agree. If not, intra-run divergence.

#eval aslrBit ()
theorem t1 : aslrBit () = true := by native_decide
theorem t2 : aslrBit () = true := by native_decide
theorem t3 : aslrBit () = true := by native_decide
#eval aslrBit ()
