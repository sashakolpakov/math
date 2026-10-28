import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NoetherianHilbertPolynomialBounds
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FieldBaseChange

/-! # Family Polynomial Bounds -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FamilyPolynomialBounds

noncomputable section

/-! Finite polynomial bounds for actual field fibers of a projective
closed family over a noetherian ring, including the saturated ideal of
the scheme-theoretic fiber. No flatness is needed for this finite bound. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding
universe u

theorem exists_finite_projective_fiber_polynomials
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).left.IdealSheafData) :
    ∃ F : Finset (Polynomial ℚ),
      ∀ (K : Type u) [Field K] (φ : R →+* K) (P : Polynomial ℚ),
        HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
          (I.comap (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n))).toIdeal P → P ∈ F := by
  obtain ⟨F, hF⟩ := NoetherianHilbertPolynomialBounds.PolarizationEmbedding.exists_finite_field_specialization_hilbertPolynomials.{u, u}
    (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I)
  refine ⟨F, fun K _ φ P hP => ?_⟩
  have h := FieldBaseChange.PolarizationEmbedding.projectiveIdeal_coefficientBaseChange (R := CommRingCat.of R)
    (A := CommRingCat.of K) I (CommRingCat.ofHom φ)
  have h₁ := congrArg (fun J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n) =>
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P) h
  exact hF K φ P ((HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff
    ((HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I).map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) P).mp
      ((Iff.of_eq h₁).mp hP))

theorem exists_finite_closed_projective_fiber_polynomials
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).left) [IsClosedImmersion j] :
    ∃ F : Finset (Polynomial ℚ),
      ∀ (K : Type u) [Field K] (φ : R →+* K) (Y : Scheme.{u})
        (e : Y ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n).left) (a : Y ⟶ X),
        IsPullback a e j (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n) →
        ∃ P ∈ F, HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf e.ker).toIdeal P := by
  obtain ⟨F, hF⟩ := exists_finite_projective_fiber_polynomials j.ker
  refine ⟨F, fun K _ φ Y e a h => ?_⟩
  obtain ⟨P, hP⟩ := HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf e.ker)
  refine ⟨P, ?_, hP⟩
  have hker := AbelianModuli.HilbertConstruction.Projective.IdealBaseChange.closedImmersion_kernel_isPullback j e a _ h
  have h₁ := congrArg (fun I : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n).left.IdealSheafData =>
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I).toIdeal P) hker
  exact hF K φ P ((Iff.of_eq h₁).mp hP)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FamilyPolynomialBounds
