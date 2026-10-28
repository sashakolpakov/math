import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantAlgebra

/-! # Determinant Monomial Transformations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantMonomialTransformations

noncomputable section

/-! Determinant monomials transform by explicit powers of the basis
determinant and the independently rescaled marked vectors. -/
open scoped BigOperators Classical
universe u v w
variable {R : Type u} [CommRing R]

theorem exponentMonomial_common_factor {κ : Type v} [Fintype κ]
    (D : κ → R) (a : κ → ℕ) (c : R) :
    Balanced.MonomialAlgebra.exponentMonomial (fun j => c * D j) a = c ^ (∑ j, a j) * Balanced.MonomialAlgebra.exponentMonomial D a := by
  simp only [Balanced.MonomialAlgebra.exponentMonomial, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]

theorem exponentMonomial_weighted_rescale {κ : Type v} [Fintype κ] {ι : Type w} [Fintype ι]
    (D : κ → R) (a : κ → ℕ) (w : κ → ι → ℕ) (c : ι → R) :
    Balanced.MonomialAlgebra.exponentMonomial (fun j => (∏ i, c i ^ w j i) * D j) a =
      (∏ i, c i ^ Balanced.ExponentFiniteGeneration.monomialMultiDegree w a i) * Balanced.MonomialAlgebra.exponentMonomial D a := by
  simp only [Balanced.MonomialAlgebra.exponentMonomial, mul_pow, Finset.prod_mul_distrib]
  congr 1
  simp_rw [← Finset.prod_pow, ← pow_mul]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Balanced.ExponentFiniteGeneration.monomialMultiDegree, Nat.mul_comm, Finset.prod_pow_eq_pow_sum]

theorem labeledDeterminant_rescaling_weight {r m : ℕ}
    (σ : Fin r → Fin m) (c : Fin m → R) :
    ∏ j, c (σ j) = ∏ i, c i ^ DeterminantBlockDegrees.labeledDeterminantWeight σ i := by
  unfold DeterminantBlockDegrees.labeledDeterminantWeight
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  symm
  calc
    (∏ i, c i ^ (if σ j = i then 1 else 0)) = ∏ i, if σ j = i then c i else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      split <;> simp_all only [pow_one, pow_zero]
    _ = c (σ j) := by simp

theorem determinantMonomial_rescale {r m : ℕ} (v : Fin m → Fin r → R)
    (a : (Fin r → Fin m) → ℕ) (c : Fin m → R) :
    Balanced.MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ (fun i j => c i * v i j)) a =
      (∏ i, c i ^ Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i) *
        Balanced.MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ v) a := by
  simp_rw [LabeledDeterminantPolynomials.labeledDeterminant_rescale, labeledDeterminant_rescaling_weight]
  exact exponentMonomial_weighted_rescale _ _ _ _

theorem determinantMonomial_linear {r m : ℕ} (v : Fin m → Fin r → R)
    (a : (Fin r → Fin m) → ℕ) (T : (Fin r → R) →ₗ[R] (Fin r → R)) :
    Balanced.MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ (fun i => T (v i))) a =
      T.det ^ (∑ σ, a σ) * Balanced.MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ v) a := by
  simp_rw [LabeledDeterminantPolynomials.labeledDeterminant_linear]
  exact exponentMonomial_common_factor _ _ _

theorem determinantMonomial_linear_rescale {r m : ℕ} (v : Fin m → Fin r → R)
    (a : (Fin r → Fin m) → ℕ) (T : (Fin r → R) →ₗ[R] (Fin r → R)) (c : Fin m → R) :
    Balanced.MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ (fun i j => c i * T (v i) j)) a =
      (T.det ^ (∑ σ, a σ) * ∏ i, c i ^ Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i) *
        Balanced.MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ v) a := by
  rw [determinantMonomial_rescale, determinantMonomial_linear]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantMonomialTransformations
