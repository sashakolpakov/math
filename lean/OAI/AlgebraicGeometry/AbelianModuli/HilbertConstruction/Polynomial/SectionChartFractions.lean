import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedPolynomialSectionMap

/-! # Section Chart Fractions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.SectionChartFractions

noncomputable section

/-! The canonical map from a homogeneous coordinate quotient to
twisting sections restricts on every standard chart to its actual
localized homogeneous fraction. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateQuotientTwistingSectionMap_cech (d : ℕ) (q : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) :
    (Projective.TwistTupleCoordinates.coordinateTwistTupleCechEquiv I d
      (Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap I d (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d q))).val =
      HilbertScheme.Presentations.Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d q) := by
  let a := (Cech.DegreeSectionsEquivalence.moduleCechAugmentationSectionsMap (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ))
      ((HilbertScheme.Presentations.Cech.AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)).symm (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d q))
  have h := congrArg (fun x : HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) => x.val.val)
      ((ProjectiveTwisting.SectionsCech.projectiveTwistingSectionsCechEquiv I d).apply_symm_apply a)
  rw [HilbertScheme.Presentations.Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap, HilbertScheme.Presentations.Cech.AugmentationMap.ProjectiveCech.moduleAugmentationToTerm_equiv]
  exact h

theorem coordinateQuotientTwistingSectionMap_chart (d : ℕ) (q : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)
    (i : Fin (n + 1)) :
    (ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I {i} i (Finset.mem_singleton_self i) d
      (Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap I d (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d q) i)).val =
      HilbertScheme.Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}) 0 (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d q).val := by
  have h := congrFun (coordinateQuotientTwistingSectionMap_cech I d q) {i}
  rw [Projective.TwistTupleCoordinates.coordinateTwistTupleCechEquiv_singleton, HilbertScheme.Presentations.Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap_singleton] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.SectionChartFractions
