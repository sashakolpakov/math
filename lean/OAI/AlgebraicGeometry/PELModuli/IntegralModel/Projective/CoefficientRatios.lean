import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FrameRatios
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality

/-! # Coefficient Ratios -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientRatios

noncomputable section

/-! Coefficient extension preserves the actual affine coordinate ratios
of projective space, including the sections used in hyperplane frames. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R K : Type u} [CommRing R] [CommRing K] {n : ℕ} (φ : R →+* K)

theorem coefficientCoordinateOpen_preimage (i : Fin (n + 1)) :
    AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n ⁻¹ᵁ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i =
      SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i := by
  change Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n) (MvPolynomial.map φ (X i)) = _
  rw [MvPolynomial.map_X]

theorem coefficientCoordinateRatio_aux (i j : Fin (n + 1))
    (t : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (ht : HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ (X i) = t) :
    (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n).appLE
      (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n) t)
      (by rw [← ht]; rfl) (Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i) (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (X j))) =
    Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n) t
      (HomogeneousLocalization.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)
        (P := Submonoid.powers (X i)) (Q := Submonoid.powers t)
        (by rintro _ ⟨m, rfl⟩; exact ⟨m, by rw [map_pow, ht]⟩)
        (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (X j))) := by
  subst t
  let : Algebra R K := φ.toAlgebra
  exact ConcreteCategory.congr_hom
    (Proj.awayToSection_comp_appLE (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)
      AbelianModuli.HilbertConstruction.Polynomial.ProjectiveCoefficients.polynomial_irrelevant_coefficient (isHomogeneous_X R i)) (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (X j))

theorem coefficientCoordinateRatio_section (i j : Fin (n + 1)) :
    (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n).appLE
      (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i)
      (coefficientCoordinateOpen_preimage φ i).ge
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j) =
        SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := K) i j := by
  rw [← FrameRatios.PolarizationEmbedding.e34_coordinateRatio_section, ← FrameRatios.PolarizationEmbedding.e34_coordinateRatio_section]
  have h := coefficientCoordinateRatio_aux φ i j (X i) (MvPolynomial.map_X φ i)
  convert h using 1
  apply congrArg (Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n) (X i))
  simp only [HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize_X, HilbertScheme.Presentations.Projective.IdealRecovery.GradedHilbert.coordinateFraction, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.map_mk]
  apply congrArg HomogeneousLocalization.mk
  ext <;> simp [HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap]

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientRatios
