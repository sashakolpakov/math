import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HilbertCoefficientTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SaturationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality

/-! # Field Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FieldBaseChange

noncomputable section

/-! The actual homogeneous ideal of a projective closed subscheme preserves
its Hilbert polynomial under any extension of coefficient fields. This
compares the scheme-theoretic pulled-back ideal, including saturation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

universe u

theorem projectiveIdeal_coefficientBaseChange
    {R A : CommRingCat.{u}} {n : ℕ}
    (I : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).left.IdealSheafData) (φ : R ⟶ A) :
    HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (I.comap (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n)) =
      HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation ((HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I).map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ.hom)) := by
  let : Algebra R A := φ.hom.toAlgebra
  have hI := HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf I
  have he : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion
      (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I))).ker =
      I.comap (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) :=
    (AbelianModuli.HilbertConstruction.Projective.IdealBaseChange.projectiveQuotientIdeal_baseChange (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I)).trans
      (congrArg (fun J => J.comap (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n)) hI)
  exact congrArg HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf he.symm

theorem projectiveIdeal_fieldBaseChange_hilbertPolynomial_iff
    {k K : Type u} [Field k] [Field K] {n : ℕ}
    (I : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace k n).left.IdealSheafData) (φ : k →+* K)
    (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (I.comap (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n))).toIdeal P ↔
        HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I).toIdeal P := by
  have h := projectiveIdeal_coefficientBaseChange (R := CommRingCat.of k)
    (A := CommRingCat.of K) I (CommRingCat.ofHom φ)
  have h₁ := congrArg (fun J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n) =>
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P) h
  exact (Iff.of_eq h₁).trans
    ((HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff
      ((HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I).map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) P).trans
        (HilbertCoefficientTransport.PolarizationEmbedding.hasHilbertPolynomial_coefficient_map_iff φ (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I) P))

theorem closedProjective_fieldBaseChange_hilbertPolynomial_iff
    {k K : Type u} [Field k] [Field K] {n : ℕ} {X Y : Scheme.{u}}
    (j : X ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace k n).left) [IsClosedImmersion j]
    (e : Y ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n).left) (a : Y ⟶ X) (φ : k →+* K)
    (h : IsPullback a e j (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n)) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf e.ker).toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf j.ker).toIdeal P := by
  have hker := AbelianModuli.HilbertConstruction.Projective.IdealBaseChange.closedImmersion_kernel_isPullback j e a _ h
  have h₁ := congrArg (fun I : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n).left.IdealSheafData =>
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I).toIdeal P) hker
  exact (Iff.of_eq h₁).trans (projectiveIdeal_fieldBaseChange_hilbertPolynomial_iff j.ker φ P)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FieldBaseChange
