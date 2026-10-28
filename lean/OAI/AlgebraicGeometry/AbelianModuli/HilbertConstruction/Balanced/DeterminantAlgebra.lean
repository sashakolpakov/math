import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantBlockDegrees

/-! # Determinant Algebra -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantAlgebra

noncomputable section

/-! The actual balanced determinant algebra is finite type, and its
common degree is positive for every nonconstant exponent when r is positive. -/
open scoped BigOperators Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {r m : ℕ}

def balancedDeterminantAlgebra (R : Type u) [CommRing R] (r m : ℕ) :
    Subalgebra R (MvPolynomial (Fin m × Fin r) R) :=
  MonomialAlgebra.balancedMonomialAlgebra R (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) DeterminantBlockDegrees.labeledDeterminantWeight

theorem balancedDeterminantAlgebra_finiteType (R : Type u) [CommRing R] (r m : ℕ) :
    Algebra.FiniteType R (balancedDeterminantAlgebra R r m) :=
  MonomialAlgebra.balancedMonomialAlgebra_finiteType _ _

theorem labeledDeterminantWeight_sum (σ : Fin r → Fin m) :
    ∑ i, DeterminantBlockDegrees.labeledDeterminantWeight σ i = r := by
  unfold DeterminantBlockDegrees.labeledDeterminantWeight
  rw [Finset.sum_comm]
  simp

theorem determinantMonomial_totalBlockDegree (a : (Fin r → Fin m) → ℕ) :
    ∑ i, ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i = r * ∑ σ, a σ := by
  unfold ExponentFiniteGeneration.monomialMultiDegree
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, labeledDeterminantWeight_sum, ← Finset.sum_mul]
  exact Nat.mul_comm _ _

theorem balancedDeterminantMonomial_degree_mass
    (a : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) (i : Fin m) :
    r * ∑ σ, a σ = m * ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i := by
  rw [← determinantMonomial_totalBlockDegree]
  have he : ∀ j, ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a j =
      ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i :=
    fun j => (ExponentFiniteGeneration.mem_balancedExponentMonoid_iff _ _).mp ha j i
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

theorem balancedDeterminantMonomial_degree_zero_iff (hr : 0 < r)
    (a : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) (i : Fin m) :
    ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hm := balancedDeterminantMonomial_degree_mass a ha i
    rw [h, Nat.mul_zero] at hm
    have hs : ∑ σ, a σ = 0 := (Nat.mul_eq_zero.mp hm).resolve_left (Nat.ne_of_gt hr)
    funext σ
    exact Finset.sum_eq_zero_iff.mp hs σ (Finset.mem_univ _)
  · rintro rfl
    simp only [ExponentFiniteGeneration.monomialMultiDegree, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantAlgebra
