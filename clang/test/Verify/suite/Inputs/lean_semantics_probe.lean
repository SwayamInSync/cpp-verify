import CppVerify.Generated

/- The generated definitions at the values where C++, SMT-LIB, and Lean's own
   operators differ. Each holds by evaluation. -/

-- Machine division by zero is SMT-LIB's, as in the solvers and the certifier.
-- Lean's own quotient gives 0 there, so the export does not use it.
example : BitVec.smtUDiv 7#8 0#8 = 255#8 := by decide
example : BitVec.smtSDiv 7#8 0#8 = 255#8 := by decide
example : BitVec.smtSDiv (-7#8) 0#8 = 1#8 := by decide
example : 7#8 / 0#8 = 0#8 := by decide
example : BitVec.umod 7#8 0#8 = 7#8 := by decide
example : BitVec.srem (-7#8) 0#8 = -7#8 := by decide

-- Signed machine division truncates, and the remainder takes the dividend's
-- sign, as in C++.
example : BitVec.smtSDiv (-7#8) 2#8 = -3#8 := by decide
example : BitVec.srem (-7#8) 2#8 = -1#8 := by decide

-- Mathematical division truncates too, and is total.
example : cppIntDiv (-7) 2 = -3 := by decide
example : cppIntRem (-7) 2 = -1 := by decide
example : cppIntDiv 7 0 = 0 := by decide
example : cppIntRem 7 0 = 7 := by decide

-- A shift by the width or more gives 0, as capped in the export.
example : 1#8 <<< min (300#16).toNat 8 = 0#8 := by decide
example : BitVec.sshiftRight (-128#8) 9 = -1#8 := by decide

-- Comparisons and Boolean cells are decided, not classical.
example : cppBvSlt (-1#8) 0#8 := by decide
example : ¬cppBvUlt (-1#8) 0#8 := by decide
example : cppBvSle 0#8 0#8 ∧ cppBvUle 255#8 255#8 := by decide
example : heapSelectBool (fun _ => 2) 0 := by decide
example : ¬heapSelectBool (fun _ => 0) 0 := by decide
