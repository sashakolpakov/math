import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.SectionHomogeneousFractions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.FunctionNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.RingSectionBasis

/-! # Polynomial Section Nonvanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PolynomialSectionNonvanishing

noncomputable section

/-! The actual twisting section attached to a homogeneous coordinate
class is nonvanishing precisely on that class's projective basic open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateQuotientActualTwistingSection (d : ℕ) (q : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) :
    Line.Bundles.structureModule (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) ⟶ (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf :=
  (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
    (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf).symm (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d q)

theorem coordinateQuotientActualTwistingSection_tuple (d : ℕ) (q : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)
    (i : Fin (n + 1)) :
    OpenFrame.CoefficientSections.openFrameGlobalTupleMap (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d)
      (Global.Sections.moduleSectionHomEquiv (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf
        (coordinateQuotientActualTwistingSection I d q)) (ULift.up i) =
      Projective.TwistGlobalTuples.projectiveTwistGlobalTupleMap I d (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d q) i := by
  have h := (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv
    (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
    (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf).apply_symm_apply (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d q)
  change Global.Sections.moduleSectionHomEquiv (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf
    (coordinateQuotientActualTwistingSection I d q) = SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d q at h
  change OpenFrame.CoefficientSections.openFrameGlobalTupleMap (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d) _ (ULift.up i) =
    OpenFrame.CoefficientSections.openFrameGlobalTupleMap (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d) _ (ULift.up i)
  exact congrArg
    (fun t => OpenFrame.CoefficientSections.openFrameGlobalTupleMap (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d) t (ULift.up i)) h

theorem coordinateQuotientActualTwistingSection_nonvanishing_chart (d : ℕ) (hd : 0 < d)
    (q : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) (i : Fin (n + 1)) :
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing (coordinateQuotientActualTwistingSection I d q) =
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι ⁻¹ᵁ
        (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ⊓ Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (Polynomial.SectionHomogeneousFractions.coordinateQuotientNumerator I d q).val) := by
  have h := OpenFrame.FunctionNonvanishing.openFrameSection_nonvanishing_chart_function (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d)
    (coordinateQuotientActualTwistingSection I d q) (ULift.up i)
  erw [coordinateQuotientActualTwistingSection_tuple,
    Polynomial.SectionHomogeneousFractions.coordinateQuotientTwistingSectionMap_chart_basicOpen I d hd] at h
  exact h

theorem coordinateQuotientActualTwistingSection_nonvanishing (d : ℕ) (hd : 0 < d)
    (q : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) :
    Ample.LineBundles.sectionNonvanishing (coordinateQuotientActualTwistingSection I d q) =
      Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (Polynomial.SectionHomogeneousFractions.coordinateQuotientNumerator I d q).val := by
  ext x
  obtain ⟨i, hi⟩ := ProjectiveTwisting.Bundle.projectiveTwistingCover I x
  let y : (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down}).toScheme := ⟨x, hi⟩
  have h := congrArg (fun V : (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down}).toScheme.Opens => y ∈ V)
    (coordinateQuotientActualTwistingSection_nonvanishing_chart I d hd q i.down)
  change (x ∈ Ample.LineBundles.sectionNonvanishing (coordinateQuotientActualTwistingSection I d q)) =
    (x ∈ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down} ∧
      x ∈ Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (Polynomial.SectionHomogeneousFractions.coordinateQuotientNumerator I d q).val) at h
  exact h.to_iff.trans (and_iff_right hi)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PolynomialSectionNonvanishing
