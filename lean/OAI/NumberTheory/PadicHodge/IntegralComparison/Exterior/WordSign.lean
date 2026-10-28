import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-! # Word Sign -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.WordSign

noncomputable section

/-! Moving one exterior generator through a word contributes its
degree sign, over an arbitrary commutative coefficient ring. -/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem generator_word (x : M) (n : ℕ) (v : Fin n → M) :
    ExteriorAlgebra.ι R x * ExteriorAlgebra.ιMulti R n v =
      (-1 : ℤ) ^ n • (ExteriorAlgebra.ιMulti R n v * ExteriorAlgebra.ι R x) := by
  induction n with
  | zero => simp only [ExteriorAlgebra.ιMulti_zero_apply, mul_one, one_mul, pow_zero, one_smul]
  | succ n ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      have hswap : ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R (v 0) =
          -(ExteriorAlgebra.ι R (v 0) * ExteriorAlgebra.ι R x) :=
        eq_neg_iff_add_eq_zero.mpr (ExteriorAlgebra.ι_add_mul_swap x (v 0))
      calc
        _ = -(ExteriorAlgebra.ι R (v 0) *
            (ExteriorAlgebra.ι R x * ExteriorAlgebra.ιMulti R n (Matrix.vecTail v))) := by
          rw [← mul_assoc, hswap, neg_mul, mul_assoc]
        _ = -(ExteriorAlgebra.ι R (v 0) *
            ((-1 : ℤ) ^ n • (ExteriorAlgebra.ιMulti R n (Matrix.vecTail v) * ExteriorAlgebra.ι R x))) := by
          rw [ih]
        _ = _ := by
          simp only [pow_succ, mul_neg_one, neg_smul, mul_smul_comm, mul_assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.WordSign
