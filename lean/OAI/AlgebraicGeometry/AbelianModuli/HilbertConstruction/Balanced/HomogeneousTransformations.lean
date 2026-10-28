import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantFractions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialSpan
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomialExponentExtension

/-! # Homogeneous Transformations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.HomogeneousTransformations

noncomputable section

/-! The transformation formula extends from monomials to every element
of the balanced homogeneous piece, so all degree-zero fractions are invariant. -/
open scoped BigOperators Classical
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] {r m : ℕ}

theorem balancedHomogeneousPolynomial_transform (hr : 0 < r)
    (v : Fin m → Fin r → A) (T : (Fin r → A) →ₗ[A] (Fin r → A)) (c : Fin m → A)
    (a : (Fin r → Fin m) → ℕ) (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (i : Fin m) (p : MvPolynomial (Fin m × Fin r) R)
    (hp : p ∈ MonomialSpan.balancedMonomialDegreeSpan (R := R) (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R)
      DeterminantBlockDegrees.labeledDeterminantWeight i (ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i)) :
    MvPolynomial.aeval (fun jk : Fin m × Fin r => c jk.1 * T (v jk.1) jk.2) p =
      (T.det ^ (∑ σ, a σ) * ∏ j, c j ^ ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a j) *
        MvPolynomial.aeval (fun jk : Fin m × Fin r => v jk.1 jk.2) p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, ⟨hb, hdeg⟩, rfl⟩ := hp
    have htrans (σ : Fin r → Fin m) := LabeledDeterminantPolynomials.labeledDeterminantPolynomial_eval (R := R) σ
      (fun j k => c j * T (v j) k)
    simpa only [MonomialAlgebra.exponentMonomial, map_prod, map_pow, htrans, LabeledDeterminantPolynomials.labeledDeterminantPolynomial_eval] using
      DeterminantFractions.balancedDeterminantMonomial_transform_common_factor hr v T c a b ha hb i hdeg
  | zero => simp only [map_zero, mul_zero]
  | add p q _ _ hp hq => simp only [map_add, hp, hq, mul_add]
  | smul s p _ hp => simp only [map_smul, hp, mul_smul_comm]

theorem balancedHomogeneousPolynomial_cross_invariant (hr : 0 < r)
    (v : Fin m → Fin r → A) (T : (Fin r → A) →ₗ[A] (Fin r → A)) (c : Fin m → A)
    (a : (Fin r → Fin m) → ℕ) (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (i : Fin m) (p q : MvPolynomial (Fin m × Fin r) R)
    (hp : p ∈ MonomialSpan.balancedMonomialDegreeSpan (R := R) (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R)
      DeterminantBlockDegrees.labeledDeterminantWeight i (ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i))
    (hq : q ∈ MonomialSpan.balancedMonomialDegreeSpan (R := R) (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R)
      DeterminantBlockDegrees.labeledDeterminantWeight i (ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i)) :
    MvPolynomial.aeval (fun jk : Fin m × Fin r => c jk.1 * T (v jk.1) jk.2) p *
        MvPolynomial.aeval (fun jk : Fin m × Fin r => v jk.1 jk.2) q =
      MvPolynomial.aeval (fun jk : Fin m × Fin r => c jk.1 * T (v jk.1) jk.2) q *
        MvPolynomial.aeval (fun jk : Fin m × Fin r => v jk.1 jk.2) p := by
  rw [balancedHomogeneousPolynomial_transform hr v T c a ha i p hp,
    balancedHomogeneousPolynomial_transform hr v T c a ha i q hq]
  ring

theorem balancedHomogeneousFraction_invariant (hr : 0 < r)
    (v : Fin m → Fin r → A) (T : (Fin r → A) →ₗ[A] (Fin r → A)) (c : Fin m → A)
    (a : (Fin r → Fin m) → ℕ) (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (i : Fin m) (p q : MvPolynomial (Fin m × Fin r) R)
    (hp : p ∈ MonomialSpan.balancedMonomialDegreeSpan (R := R) (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R)
      DeterminantBlockDegrees.labeledDeterminantWeight i (ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i))
    (hq : q ∈ MonomialSpan.balancedMonomialDegreeSpan (R := R) (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R)
      DeterminantBlockDegrees.labeledDeterminantWeight i (ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i))
    (hu : IsUnit (MvPolynomial.aeval (fun jk : Fin m × Fin r => v jk.1 jk.2) q))
    (hu' : IsUnit (MvPolynomial.aeval (fun jk : Fin m × Fin r => c jk.1 * T (v jk.1) jk.2) q)) :
    MvPolynomial.aeval (fun jk : Fin m × Fin r => c jk.1 * T (v jk.1) jk.2) p * (↑hu'.unit⁻¹ : A) =
      MvPolynomial.aeval (fun jk : Fin m × Fin r => v jk.1 jk.2) p * (↑hu.unit⁻¹ : A) :=
  Unit.MonomialFractions.unitDenominator_fraction_eq hu' hu
    (balancedHomogeneousPolynomial_cross_invariant hr v T c a ha i p q hp hq)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.HomogeneousTransformations
