import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FieldCompleteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.GlobalSections

/-! # Coordinate Completeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.CoordinateCompleteness.StableHilbertCoverage

noncomputable section

/-! The degree-one polynomial section map used for the rank argument
has exactly the original homogeneous coordinate sections as its images. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
universe u
variable {R : Type u} [CommRing R] {n : ℕ}

private theorem frameSections_ext {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
    (D : OpenFrame.Transitions.OpenFrameTransitions U)
    {s t : Line.Bundles.structureModule X ⟶ OpenFrame.ModuleSheaf.openFrameModuleSheaf D}
    (h : OpenFrame.CoefficientSections.openFrameGlobalTupleMap D (Global.Sections.moduleSectionHomEquiv (OpenFrame.ModuleSheaf.openFrameModuleSheaf D) s) =
      OpenFrame.CoefficientSections.openFrameGlobalTupleMap D (Global.Sections.moduleSectionHomEquiv (OpenFrame.ModuleSheaf.openFrameModuleSheaf D) t)) : s = t :=
  (Global.Sections.moduleSectionHomEquiv (OpenFrame.ModuleSheaf.openFrameModuleSheaf D)).injective
    ((Subtype.val_injective.comp (OpenFrame.GlobalSections.openFrameGlobalSectionsEquiv D).injective) h)

private theorem polynomialLinearSection_chart
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (i j : Fin (n + 1)) :
    Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap I 1
      (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I 1
        ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal 1).mkQ ⟨X j, isHomogeneous_X R j⟩)) i =
      Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i) := by
  apply Polynomial.SectionChartValues.coordinateSectionLocalization_injective I {i} (Finset.singleton_nonempty i)
  rw [Projective.SectionLocalization.coordinateSectionLocalization_ratio]
  apply (Coordinate.HomogeneousRatios.coordinateChartVariable_isUnit I {i} i (Finset.mem_singleton_self i)).mul_left_cancel
  have h := Polynomial.SectionChartValues.coordinateQuotientTwistingSectionMap_chart_crossMultiply I 1
    ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal 1).mkQ ⟨X j, isHomogeneous_X R j⟩) i
  have hv : (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I 1
      ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal 1).mkQ ⟨X j, isHomogeneous_X R j⟩)).val =
        HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X j) := rfl
  rw [pow_one, hv] at h
  exact h.trans (Coordinate.HomogeneousRatios.coordinateHomogeneousRatio_mul I {i} i j (Finset.mem_singleton_self i)).symm

theorem polynomialLinearSection_eq_coordinate
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (j : Fin (n + 1)) :
    Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection I 1
      ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal 1).mkQ ⟨X j, isHomogeneous_X R j⟩) =
        ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I j := by
  apply frameSections_ext (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1)
  funext z
  obtain ⟨i⟩ := z
  exact (Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection_tuple I 1 _ i).trans
    ((polynomialLinearSection_chart I i j).trans
      (congrFun (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection_tuple I j) ⟨i⟩).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.CoordinateCompleteness.StableHilbertCoverage
