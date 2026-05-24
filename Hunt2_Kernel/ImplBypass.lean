-- Probe: @[implemented_by] lets us substitute one function for another at runtime.
-- Question: does native_decide use the implementation, and if so, does
-- #print axioms reveal the mismatch?

-- Kernel: identity on Bool.
@[implemented_by Bool.not]
def liar (b : Bool) : Bool := b

-- Kernel says liar true = true (by reduction, since kernel uses the defined body).
theorem kernel_view : liar true = true := rfl
#print axioms kernel_view

-- Native_decide says liar true = false (runs Bool.not true = false).
theorem native_view : liar true = false := by native_decide
#print axioms native_view

-- Both proofs are now in the environment. The kernel accepts both because
-- the second is laundered through an opaque trust axiom that says
-- "native_decide returned true for `(liar true == false)`."
theorem contradict : (true : Bool) = false := kernel_view.symm.trans native_view
theorem boom : False := Bool.noConfusion contradict
#print axioms boom
