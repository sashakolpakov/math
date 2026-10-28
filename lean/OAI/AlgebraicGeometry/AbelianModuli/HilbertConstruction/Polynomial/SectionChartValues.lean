import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.SectionChartFractions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PowerFrameValues

/-! # Section Chart Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.SectionChartValues

noncomputable section

/-! In ordinary localized coordinate rings, the standard-chart
coefficient of a homogeneous section is its numerator divided by the
corresponding coordinate power. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
universe u
variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateQuotientTwistingSectionMap_chart_crossMultiply (d : ℕ)
    (q : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) (i : Fin (n + 1)) :
    algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (Localization.Away (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
          (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}))) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) ^ d *
      Projective.SectionLocalization.coordinateSectionLocalization I {i} ⟨i, Finset.mem_singleton_self i⟩
        (Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap I d (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d q) i) =
    algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) _ (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d q).val := by
  have h := congrArg
    (HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}))
    (SectionChartFractions.coordinateQuotientTwistingSectionMap_chart I d q i)
  erw [Projective.PowerFrameValues.coordinateChartPowerSectionEquiv_value I {i} i (Finset.mem_singleton_self i) d,
    HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv_fraction] at h
  simp only [HilbertScheme.Presentations.Module.Fractions.GradedModules.moduleDenominator, pow_zero, Localization.mk_eq_mk'] at h
  erw [IsLocalization.mk'_one] at h
  exact h

theorem coordinateSectionLocalization_injective (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    Function.Injective (Projective.SectionLocalization.coordinateSectionLocalization I s hs) :=
  (HomogeneousLocalization.val_injective _).comp (Projective.SectionLocalization.coordinateSectionHomogeneousEquiv I s hs).injective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.SectionChartValues
