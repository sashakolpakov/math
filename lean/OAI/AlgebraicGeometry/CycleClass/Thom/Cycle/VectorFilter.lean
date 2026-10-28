import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint

/-! # Vector Filter -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorFilter.Constructions

noncomputable section

/-! Discarding components away from the chosen point preserves the
actual cycle-vector class on the retained analytic neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem cycleVectorClassAt_cycleAtPoint (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B : V.carrier.Opens) [Nonempty B]
    (U : Opens V.analyticSpace)
    (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
    {L : Type} (u : L → U) (p n d : ℕ) (hd : p + n = d) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
    (hu : IsOpen (Set.range u)ᶜ) (c : Geometric.DimensionCycles.RationalDimensionCycle V p) (x : V.carrier) (C : V.carrier.Opens)
    (hUC : (U : Set V.analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver (AtPoint.Constructions.pointNeighborhood V p x c C))
    (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u) :
    Vector.Constructions.Class.cycleVectorClassAt V B U hU u p n d hd s hu c =
      Vector.Constructions.Class.cycleVectorClassAt V B U hU u p n d hd s hu (AtPoint.Constructions.cycleAtPoint V p x c) := by
  unfold Vector.Constructions.Class.cycleVectorClassAt
  rw [AtPoint.Constructions.relativeClass_eq_cycleAtPoint V p x c C U hUC (Set.range u) hc]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorFilter.Constructions
