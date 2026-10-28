import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantMonomialTransformations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.MonomialFractions

/-! # Determinant Fractions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantFractions

noncomputable section

/-! Balanced monomials of equal degree have the same transformation
factor. Their fractions consequently depend only on the projective configuration. -/
open scoped BigOperators Classical
universe u
variable {R : Type u} [CommRing R] {r m : ℕ}

theorem balancedDeterminantMonomial_orders_equal (hr : 0 < r)
    (a b : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hb : b ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) (i : Fin m)
    (hdeg : ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i = ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight b i) :
    ∑ σ, a σ = ∑ σ, b σ := by
  apply Nat.eq_of_mul_eq_mul_left hr
  rw [DeterminantAlgebra.balancedDeterminantMonomial_degree_mass a ha i,
    DeterminantAlgebra.balancedDeterminantMonomial_degree_mass b hb i, hdeg]

theorem balancedDeterminantMonomial_all_degrees_equal
    (a b : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hb : b ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) (i : Fin m)
    (hdeg : ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i = ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight b i) :
    ∀ j, ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a j = ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight b j := by
  intro j
  exact ((ExponentFiniteGeneration.mem_balancedExponentMonoid_iff _ _).mp ha j i).trans
    (hdeg.trans ((ExponentFiniteGeneration.mem_balancedExponentMonoid_iff _ _).mp hb i j))

theorem balancedDeterminantMonomial_transform_common_factor (hr : 0 < r)
    (v : Fin m → Fin r → R) (T : (Fin r → R) →ₗ[R] (Fin r → R)) (c : Fin m → R)
    (a b : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hb : b ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) (i : Fin m)
    (hdeg : ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight b i = ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i) :
    MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ (fun j k => c j * T (v j) k)) b =
      (T.det ^ (∑ σ, a σ) * ∏ j, c j ^ ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a j) *
        MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ v) b := by
  rw [DeterminantMonomialTransformations.determinantMonomial_linear_rescale,
    balancedDeterminantMonomial_orders_equal hr b a hb ha i hdeg]
  simp only [balancedDeterminantMonomial_all_degrees_equal b a hb ha i hdeg]

theorem balancedDeterminantMonomial_cross_invariant (hr : 0 < r)
    (v : Fin m → Fin r → R) (T : (Fin r → R) →ₗ[R] (Fin r → R)) (c : Fin m → R)
    (a b : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hb : b ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) (i : Fin m)
    (hdeg : ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight b i = ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i) :
    MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ (fun j k => c j * T (v j) k)) b *
        MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ v) a =
      MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ (fun j k => c j * T (v j) k)) a *
        MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ v) b := by
  rw [balancedDeterminantMonomial_transform_common_factor hr v T c a b ha hb i hdeg,
    DeterminantMonomialTransformations.determinantMonomial_linear_rescale]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantFractions
