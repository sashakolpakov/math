import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Rat

/-! # Span Division -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SpanDivision

/-! Dividing a positive integral multiple inside the original rational linear span. -/

theorem rationalSubmodule_mem_of_positive_nsmul {M : Type*} [AddCommGroup M] [Module ℚ M]
    (S : Submodule ℚ M) (x : M) (n : ℕ) (hn : 0 < n) (h : n • x ∈ S) : x ∈ S := by
  apply (S.smul_mem_iff (s := (n : ℚ)) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))).mp
  simpa only [Nat.cast_smul_eq_nsmul] using h

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SpanDivision
