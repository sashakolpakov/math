import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.NormalizationBlockDegrees
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantFrameNormalizerDeterminant
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantMonomialTransformations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingMonomialCompletion

/-! # Balanced Denominator Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BalancedDenominatorIdentity

noncomputable section

/-! The normalized balanced denominator satisfies a polynomial
identity whose other factors are explicit frame monomials. -/
open scoped BigOperators Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {r m : ℕ}

theorem normalizedBalancedDenominator_identity
    (v u : Fin m → Fin r → R) (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
    (a : (Fin r → Fin m) → ℕ) (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) (i₀ : Fin m)
    (hx : ∀ z k, u z k * Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v)
        (Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z)) =
      DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun R (Fin r)) (fun j => v (σ j)) (v e) (v z) k) :
    Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ u) a *
        Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v)
          ((Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i₀) • Frame.NormalizationBlockDegrees.allFrameCoordinateExponent σ e c) =
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v)
        (((r - 1) * ∑ τ, a τ) • Frame.ChartDenominators.frameDiscriminantExponent σ e + a) := by
  let f := fun z => Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z))
  let T := DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun R (Fin r)) (fun j => v (σ j)) (v e)
  have he : (fun z k => f z * u z k) = fun z => T (v z) := by
    funext z k
    exact (mul_comm _ _).trans (hx z k)
  have h := DeterminantMonomialTransformations.determinantMonomial_rescale u a f
  rw [he, DeterminantMonomialTransformations.determinantMonomial_linear] at h
  have hT : T.det = ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun R (Fin r))
      (fun j => v (σ j)) (v e) ^ (r - 1) := by
    simpa only [Fintype.card_fin] using DeterminantFrameNormalizerDeterminant.determinantFrameLinearMap_det (fun j => v (σ j)) (v e)
  rw [hT, ← pow_mul] at h
  have hbal : ∀ j, Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a j =
      Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i₀ := fun j => (Balanced.ExponentFiniteGeneration.mem_balancedExponentMonoid_iff _ _).mp ha j i₀
  simp only [hbal, Finset.prod_pow] at h
  rw [Balanced.MonomialAlgebra.exponentMonomial_add, NonvanishingMonomialCompletion.exponentMonomial_nsmul, NonvanishingMonomialCompletion.exponentMonomial_nsmul,
    Frame.ChartDenominators.frameDiscriminantExponent_monomial]
  simp only [Frame.NormalizationBlockDegrees.allFrameCoordinateExponent, MonomialFiniteSums.exponentMonomial_sum]
  exact (mul_comm _ _).trans h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BalancedDenominatorIdentity
