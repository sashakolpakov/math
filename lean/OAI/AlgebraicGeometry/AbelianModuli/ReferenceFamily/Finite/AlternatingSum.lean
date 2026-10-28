import Mathlib.Algebra.BigOperators.Fin

/-! # Alternating Sum -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.AlternatingSum

/-! The four-term sign convention for the original degree-two Cech
differential, in an arbitrary additive coefficient group. -/

open scoped BigOperators

theorem finite_alternatingSum_four {M : Type*} [AddCommGroup M] (f : Fin 4 → M) :
    ∑ i : Fin 4, (-1 : ℤ) ^ i.val • f i = f 0 - f 1 + f 2 - f 3 := by
  rw [Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    show (-1 : ℤ) ^ (2 : Fin 4).val = 1 by decide,
    show (-1 : ℤ) ^ (3 : Fin 4).val = -1 by decide,
    one_zsmul, neg_one_zsmul, ← sub_eq_add_neg]

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.AlternatingSum
