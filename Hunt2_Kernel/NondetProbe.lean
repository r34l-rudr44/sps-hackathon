-- Probe 1: ptrEq non-determinism via ASLR.
-- ptrAddrUnsafe leaks the heap address of a value as USize.
-- Two structurally-equal but separately-defined values *may* be CSE'd
-- by the compiler/interpreter, or *may* live at different addresses.
-- Whether they share or not can depend on ASLR + allocator state.

@[noinline] def listA : List Nat := [1, 2, 3]
@[noinline] def listB : List Nat := [1, 2, 3]

-- Print the actual addresses for evidence of run-to-run variation:
#eval (unsafe ptrAddrUnsafe listA, unsafe ptrAddrUnsafe listB)

-- Bool expression that depends on whether the two lists share an address:
def shared : Bool := unsafe (ptrAddrUnsafe listA) == (unsafe ptrAddrUnsafe listB)
#eval shared

-- Probe 2: UInt64 / Nat boundary (Agent A H4)
-- Kernel reduces over arbitrary-precision Nat; native uses machine words.
def boundaryProbe : Bool :=
  let big : UInt64 := 0xFFFFFFFFFFFFFFFF
  -- Convert to Nat (no truncation), multiply (no overflow in Nat),
  -- convert back to UInt64 (truncates to 0 because 2^64 ≡ 0 mod 2^64).
  -- Both kernel and native should agree: result = 0xFFFFFFFFFFFFFFFE
  -- (since (2^64 - 1) * 2 mod 2^64 = 2^64 - 2 = 0xFF...FE)
  (big.toNat * 2).toUInt64 == 0xFFFFFFFFFFFFFFFE

#eval boundaryProbe

-- Try native_decide on each:
-- (commented to allow #eval first; uncomment to test trust pipeline)
-- theorem t_shared : shared = false := by native_decide
-- theorem t_boundary : boundaryProbe = true := by native_decide
