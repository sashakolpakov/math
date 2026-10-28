import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CechSequence
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SectionCechTransgression
import OAI.AlgebraicGeometry.DivisorClass.Chern.First

/-! # Cocycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.Cocycle

noncomputable section

section

/-!
# ChernClass: an actual relative Cech cocycle for the first Chern class

The rational-section winding and overlap corrections give an explicit
primitive of the Chern cocycle on the reference locus. Extend these cochains
to the ambient intersections and correct the original Chern representative
by their differential. The result lies in the actual relative kernel.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CechSequence.RationalCech

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "A" => (OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T)
local notation "K" => OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechD.RationalCech.subspaceSingularPresheafComplex T A
local notation "B" => OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) T

/-- The original Chern cocycle inside the original ambient Cech total complex. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.chernTotalCocycle : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (CechSequence.RationalCech.ambientCechTotal T L.logCover) 2 :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Cech.Obj.RationalCech.locallyConstantCechToTotal T L.logCover) 2
    (LogCech.RationalCech.logDefectCocycle T L.logCover L.bundleLogCech L.bundleLogCech_cocycle)

omit [IsIntegral X.carrier] in
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.chernTotalCocycle_value :
    L.chernTotalCocycle.val = Rational.Cech.RationalCech.cechTotalInclusion L.logCover B 2 0 2 rfl
      (Cech.Obj.RationalCech.locallyConstantCechEvaluation T L.logCover 2
        (LogCech.RationalCech.logDefectCech T L.logCover L.bundleLogCech L.bundleLogCech_cocycle)) := rfl

/-- The two actual correction cochains, with the totalization sign fixed. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceTransgression : (CechSequence.RationalCech.subspaceCechTotal T A L.logCover).X 1 :=
  Rational.Cech.RationalCech.cechTotalInclusion L.logCover K 0 1 1 rfl L.referenceWindingCech -
    Rational.Cech.RationalCech.cechTotalInclusion L.logCover K 1 0 1 rfl L.referenceGaugeCech

/-- The Chern cocycle restricted to the reference locus is the negative
differential of the constructed transgression. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceTransgression_d :
    (CechSequence.RationalCech.subspaceCechTotal T A L.logCover).d 1 2 L.referenceTransgression =
      -(CechSequence.RationalCech.subspaceCechTotalRestriction T A L.logCover).f 2 L.chernTotalCocycle.val := by
  unfold Line.Bundles.AlgebraicLineBundle.referenceTransgression
  have hW := CechSequence.RationalCech.cechTotalInclusion_d_apply T L.logCover K 0 1 1 rfl L.referenceWindingCech
  have hQ := CechSequence.RationalCech.cechTotalInclusion_d_apply T L.logCover K 1 0 1 rfl L.referenceGaugeCech
  have hC := CechSequence.RationalCech.cechTotalInclusion_map_apply T L.logCover (SubspaceCechD.RationalCech.subspacePresheafRestriction T A) 2 0 2 rfl
    (Cech.Obj.RationalCech.locallyConstantCechEvaluation T L.logCover 2
      (LogCech.RationalCech.logDefectCech T L.logCover L.bundleLogCech L.bundleLogCech_cocycle))
  rw [map_sub, hW, hQ,
    L.referenceWindingCech_horizontal, L.referenceWindingCech_vertical,
    L.referenceGaugeCech_horizontal, map_zero, smul_zero, add_zero, pow_one,
    neg_one_zsmul, map_neg, L.chernTotalCocycle_value, hC]
  abel_nf

/-- Extend both correction cochains by zero on each ambient intersection. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.ambientReferenceTransgression : (CechSequence.RationalCech.ambientCechTotal T L.logCover).X 1 :=
  Rational.Cech.RationalCech.cechTotalInclusion L.logCover B 0 1 1 rfl
      (SubspaceCechD.RationalCech.subspaceCechExtension T A L.logCover 0 1 L.referenceWindingCech) -
    Rational.Cech.RationalCech.cechTotalInclusion L.logCover B 1 0 1 rfl
      (SubspaceCechD.RationalCech.subspaceCechExtension T A L.logCover 1 0 L.referenceGaugeCech)

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.ambientReferenceTransgression_restrict :
    (CechSequence.RationalCech.subspaceCechTotalRestriction T A L.logCover).f 1 L.ambientReferenceTransgression =
      L.referenceTransgression := by
  unfold Line.Bundles.AlgebraicLineBundle.ambientReferenceTransgression Line.Bundles.AlgebraicLineBundle.referenceTransgression
  have hW := CechSequence.RationalCech.cechTotalInclusion_map_apply T L.logCover (SubspaceCechD.RationalCech.subspacePresheafRestriction T A) 0 1 1 rfl
    (SubspaceCechD.RationalCech.subspaceCechExtension T A L.logCover 0 1 L.referenceWindingCech)
  have hQ := CechSequence.RationalCech.cechTotalInclusion_map_apply T L.logCover (SubspaceCechD.RationalCech.subspacePresheafRestriction T A) 1 0 1 rfl
    (SubspaceCechD.RationalCech.subspaceCechExtension T A L.logCover 1 0 L.referenceGaugeCech)
  rw [map_sub, hW, hQ]
  change Rational.Cech.RationalCech.cechTotalInclusion L.logCover K 0 1 1 rfl
      (SubspaceCechD.RationalCech.subspaceCechRestriction T A L.logCover 0 1
        (SubspaceCechD.RationalCech.subspaceCechExtension T A L.logCover 0 1 L.referenceWindingCech)) -
    Rational.Cech.RationalCech.cechTotalInclusion L.logCover K 1 0 1 rfl
      (SubspaceCechD.RationalCech.subspaceCechRestriction T A L.logCover 1 0
        (SubspaceCechD.RationalCech.subspaceCechExtension T A L.logCover 1 0 L.referenceGaugeCech)) = _
  rw [SubspaceCechD.RationalCech.subspaceCechExtension_restrict, SubspaceCechD.RationalCech.subspaceCechExtension_restrict]

/-- Correct the original Chern representative by the differential of actual
extended section data. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.supportedChernAmbientCochain : (CechSequence.RationalCech.ambientCechTotal T L.logCover).X 2 :=
  L.chernTotalCocycle.val + (CechSequence.RationalCech.ambientCechTotal T L.logCover).d 1 2 L.ambientReferenceTransgression

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.supportedChernAmbientCochain_closed :
    (CechSequence.RationalCech.ambientCechTotal T L.logCover).d 2 3 L.supportedChernAmbientCochain = 0 := by
  unfold Line.Bundles.AlgebraicLineBundle.supportedChernAmbientCochain
  rw [map_add, (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ 2 L.chernTotalCocycle.val).mp L.chernTotalCocycle.property]
  exact zero_add _ |>.trans (ConcreteCategory.congr_hom
    ((CechSequence.RationalCech.ambientCechTotal T L.logCover).d_comp_d 1 2 3) L.ambientReferenceTransgression)

/-- The correction cancels the original Chern cochain exactly on the reference locus. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.supportedChernAmbientCochain_restrict :
    (CechSequence.RationalCech.subspaceCechTotalRestriction T A L.logCover).f 2 L.supportedChernAmbientCochain = 0 := by
  have h := ConcreteCategory.congr_hom
    ((CechSequence.RationalCech.subspaceCechTotalRestriction T A L.logCover).comm 1 2) L.ambientReferenceTransgression
  change (CechSequence.RationalCech.subspaceCechTotal T A L.logCover).d 1 2
      ((CechSequence.RationalCech.subspaceCechTotalRestriction T A L.logCover).f 1 L.ambientReferenceTransgression) =
    (CechSequence.RationalCech.subspaceCechTotalRestriction T A L.logCover).f 2
      ((CechSequence.RationalCech.ambientCechTotal T L.logCover).d 1 2 L.ambientReferenceTransgression) at h
  rw [L.ambientReferenceTransgression_restrict, L.referenceTransgression_d] at h
  unfold Line.Bundles.AlgebraicLineBundle.supportedChernAmbientCochain
  rw [map_add, ← h, add_neg_cancel]

/-- The corrected Chern cocycle in the actual relative Cech total complex. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.relativeChernTotalCocycle : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (CechSequence.RationalCech.relativeCechTotal T A L.logCover) 2 :=
  ⟨CechSequence.RationalCech.relativeCechTotalLift T A L.logCover 2 L.supportedChernAmbientCochain
    L.supportedChernAmbientCochain_restrict, by
      rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff]
      exact CechSequence.RationalCech.relativeCechTotalLift_closed T A L.logCover 2 L.supportedChernAmbientCochain
        L.supportedChernAmbientCochain_restrict L.supportedChernAmbientCochain_closed⟩

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.relativeChernTotalCocycle_inclusion :
    (CechSequence.RationalCech.relativeCechTotalInclusion T A L.logCover).f 2 L.relativeChernTotalCocycle.val =
      L.supportedChernAmbientCochain :=
  CechSequence.RationalCech.relativeCechTotalLift_inclusion T A L.logCover 2 L.supportedChernAmbientCochain
    L.supportedChernAmbientCochain_restrict

/-- Forgetting relative support gives the class of the original Chern cocycle. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.relativeChernTotalCocycle_absolute_class :
    HomologicalComplex.homologyMap (CechSequence.RationalCech.relativeCechTotalInclusion T A L.logCover) 2
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (CechSequence.RationalCech.relativeCechTotal T A L.logCover) 2 L.relativeChernTotalCocycle) =
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (CechSequence.RationalCech.ambientCechTotal T L.logCover) 2 L.chernTotalCocycle := by
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ (CechSequence.RationalCech.ambientCechTotal T L.logCover) 1 _ _).mpr
  refine ⟨L.ambientReferenceTransgression, ?_⟩
  change (CechSequence.RationalCech.ambientCechTotal T L.logCover).d 1 2 L.ambientReferenceTransgression =
    (CechSequence.RationalCech.relativeCechTotalInclusion T A L.logCover).f 2 L.relativeChernTotalCocycle.val -
      L.chernTotalCocycle.val
  rw [L.relativeChernTotalCocycle_inclusion, Line.Bundles.AlgebraicLineBundle.supportedChernAmbientCochain]
  abel

/-- The existing Cech-to-singular comparison sends this relative class to
the actual public first Chern class. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.relativeChernTotalCocycle_firstChern :
    (Rational.CechComparison.RationalCech.singularCechCohomologyIso T L.logCover L.logCover_covers 2).inv
      (HomologicalComplex.homologyMap (CechSequence.RationalCech.relativeCechTotalInclusion T A L.logCover) 2
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (CechSequence.RationalCech.relativeCechTotal T A L.logCover) 2 L.relativeChernTotalCocycle)) =
      First.firstChernClassQ X L := by
  rw [L.relativeChernTotalCocycle_absolute_class]
  exact congrArg
    (fun z => (Rational.CechComparison.RationalCech.singularCechCohomologyIso T L.logCover L.logCover_covers 2).inv z)
    (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality (Cech.Obj.RationalCech.locallyConstantCechToTotal T L.logCover) 2
      (LogCech.RationalCech.logDefectCocycle T L.logCover L.bundleLogCech L.bundleLogCech_cocycle)).symm

end AlgebraicLineBundle

end

/-!
# ChernClass: local winding components of the relative Chern cocycle

The degree-two, Cech-degree-zero component of the actual relative Chern
cocycle is the earlier relative winding cocycle of the actual rational
section. Thus the constructed relative lift carries the intended local data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CechSequence.RationalCech

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "A" => (OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T)
local notation "B" => OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) T
local notation "D" => OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.Cech.RationalCech.cechDoubleComplex L.logCover B
local notation "R" => OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafComplex (ModuleCat.of ℚ ℚ) T A

/-- The ambient degree-two component is the differential of the extended winding cochain. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.supportedChernAmbientCochain_zeroColumn :
    AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal D 0 2 2 rfl L.supportedChernAmbientCochain =
      Rational.Cech.RationalCech.cechCoefficientMap L.logCover ((B).d 1 2) 0
        (SubspaceCechD.RationalCech.subspaceCechExtension T A L.logCover 0 1 L.referenceWindingCech) := by
  have hC := AlgebraicTopology.DeRham.Comparison.DoubleComplexSupport.DoubleComplex.project_iota_ne D 2 0 0 2 2 rfl rfl (by decide)
    (Cech.Obj.RationalCech.locallyConstantCechEvaluation T L.logCover 2
      (LogCech.RationalCech.logDefectCech T L.logCover L.bundleLogCech L.bundleLogCech_cocycle))
  have hW := AlgebraicTopology.DeRham.Comparison.DoubleComplexDifferential.DoubleComplex.project_d_iota_vertical D 0 1 1 rfl
    (SubspaceCechD.RationalCech.subspaceCechExtension T A L.logCover 0 1 L.referenceWindingCech)
  have hQ := AlgebraicTopology.DeRham.Comparison.DoubleComplexDifferential.DoubleComplex.project_d_iota_ne D 1 0 0 2 1 rfl rfl (by decide) (by decide)
    (SubspaceCechD.RationalCech.subspaceCechExtension T A L.logCover 1 0 L.referenceGaugeCech)
  change AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal D 0 2 2 rfl (Rational.Cech.RationalCech.cechTotalInclusion L.logCover B 2 0 2 rfl
    (Cech.Obj.RationalCech.locallyConstantCechEvaluation T L.logCover 2
      (LogCech.RationalCech.logDefectCech T L.logCover L.bundleLogCech L.bundleLogCech_cocycle))) = 0 at hC
  simp only [pow_zero, one_zsmul] at hW
  change AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal D 0 2 2 rfl ((CechSequence.RationalCech.ambientCechTotal T L.logCover).d 1 2
      (Rational.Cech.RationalCech.cechTotalInclusion L.logCover B 0 1 1 rfl
        (SubspaceCechD.RationalCech.subspaceCechExtension T A L.logCover 0 1 L.referenceWindingCech))) =
    Rational.Cech.RationalCech.cechCoefficientMap L.logCover ((B).d 1 2) 0
      (SubspaceCechD.RationalCech.subspaceCechExtension T A L.logCover 0 1 L.referenceWindingCech) at hW
  change AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal D 0 2 2 rfl ((CechSequence.RationalCech.ambientCechTotal T L.logCover).d 1 2
    (Rational.Cech.RationalCech.cechTotalInclusion L.logCover B 1 0 1 rfl
      (SubspaceCechD.RationalCech.subspaceCechExtension T A L.logCover 1 0 L.referenceGaugeCech))) = 0 at hQ
  unfold Line.Bundles.AlgebraicLineBundle.supportedChernAmbientCochain Line.Bundles.AlgebraicLineBundle.ambientReferenceTransgression
  rw [L.chernTotalCocycle_value, map_add, map_sub, map_sub, hC, hW, hQ,
    zero_add, sub_zero]

/-- On each actual logarithmic chart, the relative Chern component equals
the previously constructed relative winding cocycle of its section coordinate. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.relativeChernTotalCocycle_zeroColumn (a : Fin 1 → L.LogCoverIndex) :
    AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex L.logCover R) 0 2 2 rfl L.relativeChernTotalCocycle.val a =
      (SubspaceCechD.relativeWindingCocycle (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
        (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
        (L.logIntersectionEquation a 0) (L.logIntersectionEquation_ne_zero a 0)).val := by
  apply SubspaceCechD.relativeCochainInclusion_injective (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
    (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a)) 2
  have h := AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex.project_total_map (Rational.Cech.RationalCech.cechDoubleComplexMap L.logCover
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafInclusion (ModuleCat.of ℚ ℚ) T A)) 0 2 2 rfl L.relativeChernTotalCocycle.val
  change AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal D 0 2 2 rfl
      ((CechSequence.RationalCech.relativeCechTotalInclusion T A L.logCover).f 2 L.relativeChernTotalCocycle.val) =
    SubspaceCechD.RationalCech.relativeCechInclusion T A L.logCover 0 2
      (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex L.logCover R) 0 2 2 rfl L.relativeChernTotalCocycle.val) at h
  rw [L.relativeChernTotalCocycle_inclusion, L.supportedChernAmbientCochain_zeroColumn] at h
  have ha := congrFun h a
  change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))).d 1 2
      (SubspaceCechD.zeroExtendCochain (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
        (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a)) 1
        (WindingSingular.singularWindingCochain _ (L.logIntersectionEquation a 0)
          (L.logIntersectionEquation_ne_zero a 0))) = _ at ha
  exact ha.symm.trans (SubspaceCechD.zeroExtensionConnectingCocycle_inclusion
    (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
    (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a)) 1
    (WindingSingular.singularWindingCocycle _ (L.logIntersectionEquation a 0)
      (L.logIntersectionEquation_ne_zero a 0))).symm

/-- The local component is a genuine relative cocycle, not just a total component. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.relativeChernTotalCocycle_zeroColumn_closed (a : Fin 1 → L.LogCoverIndex) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
      (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))).d 2 3
      (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex L.logCover R) 0 2 2 rfl L.relativeChernTotalCocycle.val a) = 0 := by
  rw [L.relativeChernTotalCocycle_zeroColumn]
  exact (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ 2 _).mp
    (SubspaceCechD.relativeWindingCocycle (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
      (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
      (L.logIntersectionEquation a 0) (L.logIntersectionEquation_ne_zero a 0)).property

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.Cocycle
