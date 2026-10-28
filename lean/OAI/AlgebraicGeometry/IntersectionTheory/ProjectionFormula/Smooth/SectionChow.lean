import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SectionCycles
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.IntegralCycleDescent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowAssociativity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap

/-! # Section Chow -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SectionChow

noncomputable section

/-! The section projection identity on Chow classes, with no proper
position hypothesis on the input representatives. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (s : Y.toOver ⟶ X.toOver) [IsClosedImmersion s.left]
  (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
  [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)] (hs : s ≫ f = 𝟙 Y.toOver)
  (m n r : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
  (hd : n + r = m) (p q : ℕ)

include hs hd in
theorem chow (b : Y.RationalDimensionCycle p) (d : Y.RationalDimensionCycle q) :
    General.GeneralChowIntersection.chowMap X m p (q + r)
      (ProperCycleLinearity.cycleToChowQ X p (Cycle.flatMap f p b))
      (ChowPushforwardMap.map s n m q (q + r) (by omega) (ProperCycleLinearity.cycleToChowQ Y q d)) =
    ChowPushforwardMap.map s n m (p + q) (p + (q + r)) (by omega)
      (General.GeneralChowIntersection.chowMap Y n p q (ProperCycleLinearity.cycleToChowQ Y p b) (ProperCycleLinearity.cycleToChowQ Y q d)) := by
  obtain ⟨b', hb, hp⟩ := General.ChowMoving.properly_meeting_representatives Y n p q b d
  have hB := (ProperCycleLinearity.cycleToChowQ_eq_iff Y p b b').mpr hb
  have hflat : ProperCycleLinearity.cycleToChowQ X p (Cycle.flatMap f p b) =
      ProperCycleLinearity.cycleToChowQ X p (Cycle.flatMap f p b') := by
    apply (ProperCycleLinearity.cycleToChowQ_eq_iff X p _ _).mpr
    have h := IntegralCycleDescent.preserves_relations f m n p hb
    change Cycle.flatMap f p (b - b') ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p at h
    rwa [map_sub] at h
  rw [hB, hflat, ChowPushforwardMap.map_mk,
    General.ChowAssociativity.mk_proper X m p (q + r) _ _
      (SectionCycles.meets s f hs m n r hd p q b' d hp),
    General.ChowAssociativity.mk_proper Y n p q b' d hp,
    ChowPushforwardMap.map_mk,
    SectionCycles.cycle s f hs m n r hd p q b' d hp]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SectionChow
