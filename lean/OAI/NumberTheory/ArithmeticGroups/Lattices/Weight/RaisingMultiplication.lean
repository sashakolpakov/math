import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationNilpotence

/-! # Raising Multiplication -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingMultiplication.Construction

noncomputable section

/-! Weight-raising operators are closed under multiplication. -/

open scoped Classical
open _root_.ContinuousLinearMap

variable {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [Fintype ι]

theorem orthonormal_composition_coordinate
    (b : OrthonormalBasis ι ℝ L) (X Y : L →L[ℝ] L) (i j : ι) :
    b.repr ((X * Y) (b j)) i = ∑ r, b.repr (X (b r)) i * b.repr (Y (b j)) r := by
  calc
    _ = b.repr (X (∑ r, b.repr (Y (b j)) r • b r)) i := by rw [b.sum_repr]; rfl
    _ = _ := by
      simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
        PiLp.smul_apply, smul_eq_mul, mul_comm]

theorem weightRaisingOperators_mul
    (b : OrthonormalBasis ι ℝ L) (w : ι → ℝ) (X Y : L →L[ℝ] L)
    (hX : X ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) (hY : Y ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) :
    X * Y ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w := by
  intro i j hij
  rw [orthonormal_composition_coordinate]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hir : w i ≤ w r
  · rw [hX i r hir, zero_mul]
  · rw [hY r j (le_trans (le_of_not_ge hir) hij), mul_zero]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingMultiplication.Construction
