/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Cycle.SmoothPairCoclassOverlap

/-! # Smooth Pair Open -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Exactly normalized smooth-support coclasses on overlaps

-/

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint.Basic.ComplexSchemePoint Y)

/-- Restriction is the map induced by the inclusion of support-complement pairs. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass_restrict
    {W V : Set (ComplexPoint.Basic.ComplexSchemePoint X)} (hWV : W ⊆ V)
    (hV : V ⊆ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * (d - m))
      (AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap hWV (Set.range (ComplexPoint.Basic.Point.map i)))
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass X Y i m d z V hV) =
    ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass X Y i m d z W (hWV.trans hV) :=
  AlgebraicTopology.LocalHomology.NormalProjectionTop.Singular.chartNormalProjectionCoclass_restrict _ _ _ _ _ hWV hV

variable (z' : ComplexPoint.Basic.ComplexSchemePoint Y)

/-- Exactly normalized ambient coclass agreement for the closed-immersion charts, from
smoothness, the closed immersion, and membership in its chart overlap and image. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.exists_open_smoothClosedSupportChartCoclass_eq
    (x : ComplexPoint.Basic.ComplexSchemePoint X) (hxS : x ∈ Set.range (ComplexPoint.Basic.Point.map i))
    (hx : x ∈ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
    (hx' : x ∈ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z').source) :
    ∃ (W : Opens (ComplexPoint.Basic.ComplexSchemePoint X))
      (hW : (W : Set _) ⊆ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
      (hW' : (W : Set _) ⊆ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z').source),
      x ∈ W ∧ ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass X Y i m d z W hW =
        ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass X Y i m d z' W hW' := by
  let e := ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z
  let e' := ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z'
  have ht : e x ∈ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalTransition X Y i m d z z').source := by
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ e'.source
    rwa [e.left_inv hx]
  exact AlgebraicTopology.LocalHomology.NormalProjectionOverlap.Singular.exists_open_chartNormalProjectionCoclass_eq (d - m) e e' (Set.range (ComplexPoint.Basic.Point.map i))
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z)
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z')
    x hx ((ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff
      X Y i m d z x hx).mp hxS) hx'
    (ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalTransition X Y i m d z z' (e x) ht)
    (ComplexPoint.Basic.ComplexSchemePoint.analyticAt_closedImmersionNormalTransition_symm X Y i m d z z' (e x) ht)

end

end OAI.AlgebraicGeometry
