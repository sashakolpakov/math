import OAI.AlgebraicGeometry.ComplexMultiplication.InjectiveRelativeOpenNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedCycleSmoothSection
import OAI.AlgebraicGeometry.CycleClass.Geometric.Span

/-! # Supported Cycle -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedCycle

noncomputable section

section

/-! # The genuine native cycle class gives the literal original supported injective class -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Singular

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)

theorem originalSupportedCycleInjectiveClass_comparison :
    InjectiveRelativeOpenNaturality.originalCycleRelativeToSupportedInjectiveClass X x.val p
      (SupportedCycleRelativeClass.originalSupportedCycleRelativeClass X p x) =
    ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedInjectiveClass X x.val x.property := by
  let e := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedClassNormalizationIso X x.val x.property
  let a := InjectiveRelativeOpenNaturality.originalCycleRelativeToSupportedInjectiveClass X x.val p
    (SupportedCycleRelativeClass.originalSupportedCycleRelativeClass X p x)
  have h : e.hom a = ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportCoclassSection X x.val x.property := by
    rw [CycleLowestNormalization.originalCycleNormalization_relative,
      InjectiveRelativeOpenNaturality.originalCycleSmoothRelativeClass_fromRelativeClass]
    exact SupportedCycleSmoothSection.originalSupportedCycleRelativeClass_smoothSection X p x
  calc
    a = e.inv (e.hom a) := e.addCommGroupIsoToAddEquiv.symm_apply_apply a |>.symm
    _ = e.inv (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportCoclassSection X x.val x.property) := congrArg e.inv h
    _ = ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedInjectiveClass X x.val x.property := rfl

end

section

/-! # The original supported class is the inverse of the actual relative comparison -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf _root_.HomologicalComplex
attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

theorem degreeTransport_roundtrip {α : Sort*} (A : α → Sort*) {i j : α}
    (h : i = j) (g : j = i) (z : A i) : g ▸ (h ▸ z) = z := by
  cases h
  rfl

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)
local notation "S" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x.val

theorem originalSupportedCycleInverse :
    ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafSupportedClass X x.val x.property =
    (ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedInjectiveHomology X (S) (2 * p)).symm
      ((ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X (S) ⊤ (2 * p)).symm
        (SupportedCycleRelativeClass.originalSupportedCycleRelativeClass X p x)) := by
  let z := (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X (S) ⊤ (2 * p)).symm
    (SupportedCycleRelativeClass.originalSupportedCycleRelativeClass X p x)
  have he : 2 * (p : ℤ) = ((2 * p : ℕ) : ℤ) := by omega
  have hc := originalSupportedCycleInjectiveClass_comparison X p x
  change InjectiveRelativeOpenNaturality.originalCycleSupportedDegreeClass X x.val p z =
    ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedInjectiveClass X x.val x.property at hc
  change (ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedInjectiveHomology X (S) (2 * p)).symm
    (he ▸ ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedInjectiveClass X x.val x.property) = _
  rw [← hc]
  apply congrArg (ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedInjectiveHomology X (S) (2 * p)).symm
  exact degreeTransport_roundtrip
    (fun n => ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⊤).mapHomologicalComplex
      ℤᵘᵖ).obj (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (S)))).homology n) he.symm he z

end

/-! # The same genuine native cycle class in the two spellings of its even degree -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

def nativeAbsoluteCycleClass (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    V.rationalCohomology (2 * p) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ)
    (TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ
    (2 * p) D.rationalSupportedCycleClass

theorem nativeRationalCycleClass_transport (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    D.rationalCycleClass = (two_mul p) ▸ nativeAbsoluteCycleClass D := by
  unfold CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.rationalCycleClass
  apply eq_of_heq
  exact (cast_heq _ (nativeAbsoluteCycleClass D)).trans
    (@eqRec_heq ℕ (fun n => V.rationalCohomology n)
      (2 * p) (p + p) (two_mul p) (nativeAbsoluteCycleClass D)).symm

theorem nativeRationalCycleClass_untransport (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (two_mul p).symm ▸ D.rationalCycleClass = nativeAbsoluteCycleClass D := by
  have h := congrArg (fun z => (two_mul p).symm ▸ z)
    (nativeRationalCycleClass_transport D)
  exact h.trans (degreeTransport_roundtrip (fun n => V.rationalCohomology n)
    (two_mul p) (two_mul p).symm (nativeAbsoluteCycleClass D))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedCycle
