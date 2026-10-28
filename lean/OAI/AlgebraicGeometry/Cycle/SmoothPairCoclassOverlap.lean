/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Cycle.LocalLocalHomology
import OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicChartsAt
import OAI.AlgebraicTopology.LocalHomology.NormalProjectionOverlap

/-! # Smooth Pair Coclass Overlap -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Exactly normalized smooth-support coclasses on overlaps

The local normal coclass is the pullback of the fixed complex
normal coclass along the normal coordinate projection. The holomorphic
closed-immersion charts prove that these coclasses agree on sufficiently small common ambient
neighborhoods.
-/

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint.Basic.ComplexSchemePoint Y)

/-- Let `i: Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`. Put `S =
i(Y(ℂ))` and `c = d-m`. For `z ∈ Y(ℂ)` and a subset `W` of the chosen normal chart at `i(z)`,
this class in `H^{2c}(W,W \ S;ℚ)` is the pullback of the class in `H^{2c}(ℂ^c,ℂ^c \ {0};ℚ)`
evaluating to `1` on the complex orientation class. The map of pairs uses the normal coordinate,
whose zero set is `S`. -/
def ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass (W : Set (ComplexPoint.Basic.ComplexSchemePoint X))
    (hW : W ⊆ (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair W
      -- `Y(ℂ) ⊆ X(ℂ)`, the image of the closed immersion `i`.
      (Set.range (ComplexPoint.Basic.Point.map i)))
      -- Twice the codimension of `Y` in `X`.
      (2 * (d - m)) :=
  AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass (Fin m → ℂ) (d - m)
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z)
    (Set.range (ComplexPoint.Basic.Point.map i))
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z) W hW

end

end OAI.AlgebraicGeometry
