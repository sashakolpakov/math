import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleSupport
import OAI.AlgebraicGeometry.ComplexMultiplication.OpenChartRestriction
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement
import OAI.AlgebraicGeometry.ComplexMultiplication.ManifoldDimensionBridge

/-! # Regular Ambient Manifold -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularAmbientManifold

noncomputable section

section

/-! # The same regular cycle points and the same ambient open scheme -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)

local notation "D" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports.originalDimensionSupport X p x
local notation "Y" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x.val
local notation "OX" => OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x.val

/-- Only the associativity proof for the unchanged structure map differs. -/
def originalRegularCyclePoint (q : (D).regularAnalyticSpace) : ComplexPoint.Basic.ComplexSchemePoint (Y) :=
  Over.homMk q.left (by
    rw [← CycleSupport.originalDimensionSupport_regularToBase X p x]
    exact q.w)

@[simp] theorem originalRegularCyclePoint_left (q : (D).regularAnalyticSpace) :
    (originalRegularCyclePoint X p x q).left = q.left := rfl

/-- The genuine regular locus has the original ambient dimension minus the codimension. -/
theorem originalRegularCycleModelDimension :
    (D).regularComplexDimension = OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left - p := by
  rw [(D).regularComplexDimension_eq_sub]
  exact congrArg (fun n => n - p) (ManifoldDimensionBridge.functionFieldDifferentialDimension_eq_originalDimension X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original closed lift followed by the open inclusion is the actual native regular map. -/
theorem originalRegularCyclePoint_ambient (q : (D).regularAnalyticSpace) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
      (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val))
      (ComplexPoint.Basic.Point.map (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x.val)
        (originalRegularCyclePoint X p x q)) = (D).regularAnalyticToAmbient q := by
  apply Over.OverMorphism.ext
  change (q.left ≫ Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift X x.val) ≫
      (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val).ι =
    q.left ≫ ((Cycle.Support.cycleComponentι X.left x.val ≫ X.hom).smoothLocus.ι ≫
      Cycle.Support.cycleComponentι X.left x.val)
  rw [Category.assoc, Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift_ι]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ambient open is nonempty because it contains the actual regular support. -/
theorem originalRegularCycleAmbientOpen_nonempty :
    Nonempty (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val) := by
  let q := Classical.arbitrary (D).regularAnalyticSpace
  exact ⟨ComplexPoint.Basic.Point.underlying
    (ComplexPoint.Basic.Point.map (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x.val)
      (originalRegularCyclePoint X p x q))⟩

end

/-! # The original ambient open and the native regular ambient manifold -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)

local notation "D" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports.originalDimensionSupport X p x
local notation "Y" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x.val
local notation "OX" => OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x.val

/-- The unchanged regular points, with only their structure-map associativity transported. -/
def originalRegularCyclePointEquiv : (D).regularAnalyticSpace ≃ ComplexPoint.Basic.ComplexSchemePoint (Y) where
  toFun := originalRegularCyclePoint X p x
  invFun q := Over.homMk q.left (by
    change q.left ≫ (D).regularToBase = 𝟙 _
    rw [CycleSupport.originalDimensionSupport_regularToBase X p x]
    exact q.w)
  left_inv q := Over.OverMorphism.ext rfl
  right_inv q := Over.OverMorphism.ext rfl

instance originalRegularAmbientScheme_nonempty : Nonempty (OX).left :=
  originalRegularCycleAmbientOpen_nonempty X p x

instance originalRegularAmbientScheme_integral : IsIntegral (OX).left :=
  isIntegral_of_isOpenImmersion (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val).ι

instance originalRegularAmbientNativePoints_nonempty : Nonempty (AnalyticIntrinsicAtlasRegular.NativePointManifold (OX)) :=
  ⟨ComplexPoint.Basic.Point.map (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x.val)
    (originalRegularCyclePoint X p x (Classical.arbitrary (D).regularAnalyticSpace))⟩

instance originalRegularAmbientScheme_smooth : Smooth (OX).hom :=
  inferInstanceAs (Smooth ((Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val).ι ≫ X.hom))

instance originalRegularAmbientInclusion_openImmersion :
    IsOpenImmersion (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val)).left :=
  inferInstanceAs (IsOpenImmersion (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val).ι)

theorem originalRegularAmbientDimension : OAI.Topology.Dimension.Basic.TopologicalSpace.dim (OX).left = OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left :=
  AlgebraicGeometry.Smooth.Equidimensional.SmoothOfRelativeDimension.dim_eq (f := (OX).hom) (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)

/-- The actual open inclusion, from original points to the native ambient manifold. -/
def originalRegularAmbientPointPartialHomeomorph :
    OpenPartialHomeomorph (ComplexPoint.Basic.ComplexSchemePoint (OX)) (AnalyticIntrinsicAtlasRegular.NativePointManifold X) :=
  OpenChartRestriction.originalOpenImmersionPointPartialHomeomorph
    (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem originalRegularAmbientPointPartialHomeomorph_target :
    (originalRegularAmbientPointPartialHomeomorph X p x).target =
      ((D).regularAmbientOpen : Set (BundledAbelianBridge.originalIntegralProjectiveVariety X).analyticSpace) := by
  have ht : (originalRegularAmbientPointPartialHomeomorph X p x).target =
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
        (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x.val))) := by
    simp only [originalRegularAmbientPointPartialHomeomorph,
      OpenChartRestriction.originalOpenImmersionPointPartialHomeomorph, OpenPartialHomeomorph.trans_target,
      Homeomorph.toOpenPartialHomeomorph_target, Set.preimage_univ, Set.inter_univ]
    simp only [IntrinsicOpenImmersionDifferentiable.nativeOpenImmersionPointPartialHomeomorph,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  rw [ht, (D).regularAmbientOpen_coe, CycleSupport.originalDimensionSupport_singularBoundary X p x]
  exact ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusAmbientOpen_analytic_image X x.val

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RegularAmbientManifold
