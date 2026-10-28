import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.PowerFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.RingLocalizationScalars

/-! # Power Frame Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PowerFrameValues

noncomputable section

/-! Positive-degree chart frames are multiplication by the corresponding coordinate power in the ordinary localized coordinate ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateChartPowerSectionEquiv_value (s : Finset (Fin (n + 1))) (i : Fin (n + 1))
    (hi : i ∈ s) (d : ℕ)
    (x : Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) :
    HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)
      (ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I s i hi d x).val =
    algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (Localization.Away (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
          (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s))) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) ^ d *
      SectionLocalization.coordinateSectionLocalization I s ⟨i, hi⟩ x := by
  change HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)
    ((X i : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ d • (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I s ⟨i, hi⟩ x).val) = _
  have he := Module.RingLocalizationScalars.moduleRingLocalizationEquiv_scalar (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s) ((X i : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ d)
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I s ⟨i, hi⟩ x).val
  have hx := SectionLocalization.coordinateSectionLocalization_value I s ⟨i, hi⟩ x
  have ha : algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)
      (Localization.Away (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s))) ((X i : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) ^ d) =
      algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) _ (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) ^ d := by
    rw [map_pow]
    rfl
  exact he.trans (congrArg₂ (fun a b => a * b) ha hx)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PowerFrameValues
