/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Cycle.ComponentSingularGe
import OAI.AlgebraicGeometry.ClosedImmersion.SourceOpenIs
import OAI.AlgebraicGeometry.Cycle.ComponentClosedPointDimension

/-! # Component Smooth Closed Lift -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# The smooth-locus closed lift of an integral cycle component

The ambient open is the complement of the first canonical singular-boundary support, and
the smooth locus embeds closed in it. Its constant relative dimension is `d-p`, by smooth
equidimensionality together with the coheight formula for a closed point of the integral
component.
-/

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. This is the Zariski open subset `X \ Z_sing`, obtained by
removing the singular locus of `Z`, viewed as a closed subset of `X`. -/
def Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen : X.left.Opens :=
  (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x 0).compl

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. This is the open subscheme `X \ Z_sing` together with its
structure morphism to `Spec ℂ`, restricted from that of `X`. -/
abbrev Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver : Over (Spec ↧ℂ) :=
  ComplexPoint.Basic.ComplexSchemePoint.openScheme X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x)

instance Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver_locallyOfFiniteType :
    LocallyOfFiniteType (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x).hom := by
  change LocallyOfFiniteType ((Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom)
  infer_instance

instance Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenInclusion_isImmersion :
    IsImmersion
      (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x)).left := by
  change IsImmersion (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x).ι
  infer_instance

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. The smooth locus `Z_reg` is closed in `X \ Z_sing`. This is its
closed immersion into that open subscheme, obtained by restricting the inclusion `Z → X`. -/
def Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift :
    (Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.toScheme ⟶
      (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x).toScheme :=
  ClosedImmersion.SourceOpen.closedImmersionSourceOpenLift (Cycle.Support.cycleComponentι X.left x) (Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift_isClosedImmersion :
    IsClosedImmersion (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift X x) := by
  dsimp [Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift]
  infer_instance

omit [IsIntegral X.left] [Smooth X.hom] in
@[reassoc (attr := simp)]
theorem Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift_ι :
    Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift X x ≫ (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x).ι =
      (Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫ Cycle.Support.cycleComponentι X.left x :=
  ClosedImmersion.SourceOpen.closedImmersionSourceOpenLift_ι _ _

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. This is the closed immersion `Z_reg → X \ Z_sing` as a morphism
of schemes over `ℂ`; both structure maps are induced by that of `X`. -/
def Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver :
    ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x ⟶
      Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x :=
  Over.homMk (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift X x) (by
    change Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift X x ≫
      ((Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom) =
        ((Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
          Cycle.Support.cycleComponentι X.left x) ≫ X.hom
    rw [← Category.assoc, Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift_ι])

instance Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver_isClosedImmersion :
    IsClosedImmersion (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x).left := by
  change IsClosedImmersion (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift X x)
  infer_instance

variable {d p : ℕ} [SmoothOfRelativeDimension d X.hom]

/-- The ambient open retains the original smooth relative dimension. These stay generic in
`d`: they are instances, found by resolution, and narrowing them to `dim X.left` would make
them fire less often. -/
instance Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen_smoothOfRelativeDimension :
    SmoothOfRelativeDimension d ((Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom) := by
  simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d
    (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x).ι X.hom

instance Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver_smoothOfRelativeDimension :
    SmoothOfRelativeDimension d (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x).hom := by
  change SmoothOfRelativeDimension d
    ((Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom)
  infer_instance

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. This is `Z(ℂ)` as a closed subset of the analytic space `X(ℂ)`,
namely the complex points whose underlying scheme points lie in `Z`. -/
def ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport : Closeds (ComplexPoint.Basic.ComplexSchemePoint X) :=
  ⟨Cycle.Support.cycleComponentSupport X x, Cycle.SupportEq.isClosed_cycleComponentSupport X x⟩

end

end OAI.AlgebraicGeometry
