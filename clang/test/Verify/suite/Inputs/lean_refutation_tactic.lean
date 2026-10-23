import CppVerify.Auto

-- An instance that holds: the refutation says Lean decides it true.
example : ¬ (∀ x : Int, x = 1 → x > 0) := by
  intro h
  have h₁ := h 1
  cppverify_refute h₁

opaque cppverify_unknown : Int

-- An instance about a constant Lean has no value for: the refutation says
-- Lean cannot decide it.
example : ¬ (∀ x : Int, x = 0 → x = cppverify_unknown) := by
  intro h
  have h₁ := h 0
  cppverify_refute h₁
