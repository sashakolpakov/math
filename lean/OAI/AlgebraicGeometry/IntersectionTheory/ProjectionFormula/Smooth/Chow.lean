import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Moving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.IntegralCycleDescent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowAssociativity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap

/-! # Chow -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Chow

noncomputable section

/-! The full Chow projection identity for smooth morphisms with
geometrically integral fibers, in all codimensions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
  [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)]
  (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

include m n in
theorem flat_congr (p : ℕ) (a a' : Y.RationalDimensionCycle p) (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent Y p a a') :
    ProperCycleLinearity.cycleToChowQ X p (Cycle.flatMap f p a) = ProperCycleLinearity.cycleToChowQ X p (Cycle.flatMap f p a') := by
  apply (ProperCycleLinearity.cycleToChowQ_eq_iff X p _ _).mpr
  have h := IntegralCycleDescent.preserves_relations f m n p ha
  change Cycle.flatMap f p (a - a') ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p at h
  rwa [map_sub] at h

variable (p q s : ℕ) (hd : q + n = s + m)

theorem single (a : Y.RationalDimensionCycle p) (W : X.DimensionCycleSupport q) :
    ChowPushforwardMap.map f m n (p + q) (p + s) (by omega)
      (General.GeneralChowIntersection.chowMap X m p q (ProperCycleLinearity.cycleToChowQ X p (Cycle.flatMap f p a))
        (ProperCycleLinearity.cycleToChowQ X q (Finsupp.single W 1))) =
      General.GeneralChowIntersection.chowMap Y n p s (ProperCycleLinearity.cycleToChowQ Y p a)
        (ChowPushforwardMap.map f m n q s hd (ProperCycleLinearity.cycleToChowQ X q (Finsupp.single W 1))) := by
  obtain ⟨a', ha, hpX, hpY, he⟩ := Moving.Projection.representatives f m n p q s hd a W
  rw [(ProperCycleLinearity.cycleToChowQ_eq_iff Y p a a').mpr ha, flat_congr f m n p a a' ha,
    ChowPushforwardMap.map_mk,
    General.ChowAssociativity.mk_proper X m p q _ _ hpX,
    General.ChowAssociativity.mk_proper Y n p s _ _ hpY,
    ChowPushforwardMap.map_mk, he]

theorem chow (a : Y.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    ChowPushforwardMap.map f m n (p + q) (p + s) (by omega)
      (General.GeneralChowIntersection.chowMap X m p q (ProperCycleLinearity.cycleToChowQ X p (Cycle.flatMap f p a)) (ProperCycleLinearity.cycleToChowQ X q b)) =
      General.GeneralChowIntersection.chowMap Y n p s (ProperCycleLinearity.cycleToChowQ Y p a)
        (ChowPushforwardMap.map f m n q s hd (ProperCycleLinearity.cycleToChowQ X q b)) := by
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [map_add, hb, hc]
  | single W r =>
    have hr : Finsupp.single W r = r • Finsupp.single W (1 : ℚ) := by simp
    rw [hr]
    simp only [map_smul, Projection.single f m n p q s hd a W]

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Chow
