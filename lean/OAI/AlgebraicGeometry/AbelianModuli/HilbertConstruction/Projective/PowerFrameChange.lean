import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PowerFrameValues

/-! # Power Frame Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PowerFrameChange

noncomputable section

/-! Changing the coordinate frame multiplies its coefficient by the corresponding projective coordinate ratio to the twist degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateChartPowerSectionEquiv_change (s : Finset (Fin (n + 1))) (i j : Fin (n + 1))
    (hi : i ∈ s) (hj : j ∈ s) (d : ℕ)
    (x : Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) :
    ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I s i hi d ((Coordinate.RatioSections.coordinateRatioSection I s i j hi) ^ d * x) =
      ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I s j hj d x := by
  apply Subtype.ext
  apply (HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s)).injective
  rw [PowerFrameValues.coordinateChartPowerSectionEquiv_value, PowerFrameValues.coordinateChartPowerSectionEquiv_value,
    map_mul, map_pow]
  have hr := SectionLocalization.coordinateSectionLocalization_ratio I s ⟨i, hi⟩ i j hi
  rw [hr, ← mul_assoc]
  have he := congrArg (fun a => a ^ d) (Coordinate.HomogeneousRatios.coordinateHomogeneousRatio_mul I s i j hi)
  rw [mul_pow] at he
  exact congrArg (fun a => a * SectionLocalization.coordinateSectionLocalization I s ⟨i, hi⟩ x) he

theorem coordinateChartPowerSectionEquiv_eq_iff (s : Finset (Fin (n + 1))) (i j : Fin (n + 1))
    (hi : i ∈ s) (hj : j ∈ s) (d : ℕ)
    (x y : Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)) :
    ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I s i hi d x = ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I s j hj d y ↔
      x = Coordinate.RatioSections.coordinateRatioSection I s i j hi ^ d * y := by
  rw [← coordinateChartPowerSectionEquiv_change I s i j hi hj d y]
  exact (ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I s i hi d).injective.eq_iff

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PowerFrameChange
