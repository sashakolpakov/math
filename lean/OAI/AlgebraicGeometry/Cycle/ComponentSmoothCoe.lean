/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Cycle.ComponentSmoothClosedLift

/-! # Component Smooth Coe -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# The smooth-locus closed lift of an integral cycle component

-/

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)

omit [IsIntegral X.left] [Smooth X.hom] in
/-- `X ∖ Z_sing` is the complement of the image of the component's singular locus: the
filtration index `0` in the definition contributes nothing. -/
@[simp] theorem Cycle.ComponentSmoothCoe.coe_cycleComponentSmoothLocusAmbientOpen :
    (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x : Set X.left) =
      (Cycle.Support.cycleComponentι X.left x ''
        (Stratification.Basic.singularLocusClosed (Cycle.Support.cycleComponentι X.left x ≫ X.hom) : Set _))ᶜ := rfl

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The image of the lift is the restriction of the full component support. -/
theorem Cycle.ComponentSmoothCoe.range_cycleComponentSmoothLocusClosedLift :
    Set.range (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift X x) =
      (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x).ι ⁻¹' closure ({x} : Set X.left) := by
  rw [← Cycle.SupportEq.range_cycleComponentι X.left x]
  exact ClosedImmersion.SourceOpen.range_closedImmersionSourceOpenLift _ _

variable {p : ℕ}

/-- The smooth locus has the relative dimension of the integral component, constantly. -/
theorem Cycle.ComponentSmoothCoe.cycleComponentSmoothLocus_smoothOfRelativeDimension (hx : Order.coheight x = p) :
    SmoothOfRelativeDimension (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p)
      ((Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫ Cycle.Support.cycleComponentι X.left x ≫ X.hom) := by
  let A := (Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus
  let g := A.ι ≫ Cycle.Support.cycleComponentι X.left x ≫ X.hom
  let : Smooth g := Cycle.SupportEq.cycleComponent_smoothLocus_smooth X x
  obtain ⟨m, hm⟩ := AlgebraicGeometry.Smooth.Equidimensional.exists_smoothOfRelativeDimension g
  obtain ⟨z, hzA, hzClosed⟩ := (Cycle.ComponentNormal.dense_cycleComponent_smooth_closedPoints X x).nonempty
  let zA : A.toScheme := ⟨z, hzA⟩
  have hzAClosed : IsClosed ({zA} : Set A) := by
    have he : A.ι ⁻¹' ({z} : Set (Cycle.Support.cycleComponent X.left x)) = {zA} := by
      ext a
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    exact he ▸ hzClosed.preimage A.ι.continuous
  have hmEq : m = Topology.Dimension.Basic.TopologicalSpace.dim X.left - p := by
    exact_mod_cast calc
      (m : ℕ∞) = Order.coheight zA :=
        (Cycle.ComponentNormalCoordinates.SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
          (f := g) (d := m) zA hzAClosed).symm
      _ = Order.coheight z := (coheight_eq_of_isOpenImmersion (x := zA) A.ι).symm
      _ = Topology.Dimension.Basic.TopologicalSpace.dim X.left - p := Cycle.ComponentClosedPointDimension.cycleComponent_closedPoint_coheight_eq_sub X x z hx hzClosed
  subst m
  exact hm

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The analytic image of the algebraic boundary complement is the open used by the original
ambient supported resolution. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusAmbientOpen_analytic_image :
    Set.range (ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x))) =
      ((ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x 0).compl : Set (ComplexPoint.Basic.ComplexSchemePoint X)) := by
  rw [ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion X]
  change (ComplexPoint.Basic.Point.underlying : ComplexPoint.Basic.ComplexSchemePoint X → X.left) ⁻¹'
      Set.range (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x).ι = _
  rw [Scheme.Opens.range_ι]
  rfl

/-- The complex-point image of the closed lift is precisely the restricted full support. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusClosedLift_complexPoints_range :
    Set.range (ComplexPoint.Basic.Point.map (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x)) =
      ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x)) ⁻¹'
          (Cycle.Support.cycleComponentSupport X x) := by
  rw [ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion]
  change (ComplexPoint.Basic.Point.underlying : ComplexPoint.Basic.ComplexSchemePoint (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x) →
    (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x).left) ⁻¹'
      Set.range (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLift X x) = _
  rw [Cycle.ComponentSmoothCoe.range_cycleComponentSmoothLocusClosedLift]
  rfl

end

end OAI.AlgebraicGeometry
