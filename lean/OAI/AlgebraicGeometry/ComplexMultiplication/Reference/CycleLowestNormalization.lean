import OAI.AlgebraicGeometry.ComplexMultiplication.OpenRestrictedSectionNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.InjectiveSupportSheafNormalization

/-! # Cycle Lowest Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleLowestNormalization

noncomputable section

section

/-! # The unchanged cycle-component purity comparison is the canonical sheaf class -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint _root_.TopCat.Sheaf

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem originalCycleLowestComparison_eq_classMap :
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx).hom =
      AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))
        (2 * (p : ℤ)) (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x) := by
  let K : CochainComplex
      (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
        AddCommGrpCat.{0}) ℤ :=
    ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)
  let : K.IsStrictlyGE 0 := ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex_isStrictlyGE X _
  unfold ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportLowestSectionCohomologyIso
  exact OpenRestrictedSectionNormalization.openRestrictedLowestSectionCohomologyIso_normalization
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)
    K
    0 (2 * (p : ℤ)) _ _

end

/-! # The original cycle normalization takes the actual local relative class -/

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- Restriction to the original singular-boundary complement, followed by actual relative cochains. -/
def originalCycleSmoothRelativeClass (a : ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSupportedCohomology X x p) :
    AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x : Set (ComplexPoint.Basic.ComplexSchemePoint X))
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint.Basic.ComplexSchemePoint X))) (2 * p) :=
  have he : 2 * (p : ℤ) = ((2 * p : ℕ) : ℤ) := by omega
  ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x) (2 * p)
    (he ▸ (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportExtensionIso X x hx).hom a)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem originalCycleNormalization_relative (a : ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSupportedCohomology X x p) :
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedClassNormalizationIso X x hx).hom a =
      (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x) (2 * p)).app
        (op (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x))
        (originalCycleSmoothRelativeClass X x hx a) := by
  have he : 2 * (p : ℤ) = ((2 * p : ℕ) : ℤ) := by omega
  have h := ConcreteCategory.congr_hom
    (InjectiveSupportSheafNormalization.injectiveSupportSheaf_normalization X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)
      (2 * p) (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x))
    (he ▸ (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportExtensionIso X x hx).hom a)
  unfold ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedClassNormalizationIso
  dsimp only
  simp only [Iso.trans_hom]
  rw [originalCycleLowestComparison_eq_classMap]
  simpa only [originalCycleSmoothRelativeClass] using! h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleLowestNormalization
