import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Embedding
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ChowMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap

/-! # Chow -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Chow

noncomputable section

section

/-! Divisor Chow intersection commutes with embedding an open and closed
subpresentation, using the native proper pushforward. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Embedding

variable {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (i : V.toOver ⟶ X.toOver)
  [IsOpenImmersion i.left] [IsClosedImmersion i.left]
  (m : ℕ) [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]

theorem divisor (q : ℕ) (a : X.RationalDimensionCycle 1) (b : V.RationalDimensionCycle q) :
    Divisor.ChowMap.map X m q (ProperCycleLinearity.cycleToChowQ X 1 a) (ProperCycleLinearity.cycleToChowQ X q (CycleMaps.embed i m q b)) =
      ChowPushforwardMap.map i m m (1 + q) (1 + q) rfl
        (Divisor.ChowMap.map V m q (ProperCycleLinearity.cycleToChowQ V 1 (CycleMaps.restrict i m 1 a)) (ProperCycleLinearity.cycleToChowQ V q b)) := by
  obtain ⟨u, hu, hp, _⟩ := Divisor.SimultaneousMoving.move_pair X m q a (CycleMaps.embed i m q b) (CycleMaps.embed i m q b)
  have hr : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent V 1 (CycleMaps.restrict i m 1 a) (CycleMaps.restrict i m 1 u) := by
    change CycleMaps.restrict i m 1 a - CycleMaps.restrict i m 1 u ∈ _
    rw [← map_sub]
    exact Embedding.restrict_preserves_divisor_relations i m hu
  have hp' := Embedding.meetProperly_restrict i m 1 q _ _ hp
  rw [CycleMaps.restrict_embed] at hp'
  rw [(ProperCycleLinearity.cycleToChowQ_eq_iff X 1 a u).mpr hu,
    (ProperCycleLinearity.cycleToChowQ_eq_iff V 1 _ _).mpr hr,
    Divisor.ChowMap.of_bilinear X m q _ _ hp,
    Divisor.ChowMap.of_bilinear V m q _ _ hp', ChowPushforwardMap.map_mk]
  apply congrArg (ProperCycleLinearity.cycleToChowQ X (1 + q))
  rw [Embedding.intersection_embed i m 1 q u b hp, CycleMaps.embed_eq_pushforward]

end

/-! Restriction of divisor Chow classes to an open and closed part,
and its compatibility with embedded Chow intersections. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace DivisorRestriction

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps

variable {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (i : V.toOver ⟶ X.toOver)
  [IsOpenImmersion i.left] (m : ℕ)
  [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]

def map : ProperCycleLinearity.ChowQ X 1 →ₗ[ℚ] ProperCycleLinearity.ChowQ V 1 :=
  (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1).liftQ ((ProperCycleLinearity.cycleToChowQ V 1).comp (CycleMaps.restrict i m 1)) (by
    intro a ha
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Embedding.restrict_preserves_divisor_relations i m ha)

theorem map_mk (a : X.RationalDimensionCycle 1) :
    map i m (ProperCycleLinearity.cycleToChowQ X 1 a) = ProperCycleLinearity.cycleToChowQ V 1 (CycleMaps.restrict i m 1 a) := rfl

theorem map_push (a : ProperCycleLinearity.ChowQ V 1) :
    map i m (ChowPushforwardMap.map i m m 1 1 rfl a) = a := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective V 1 a
  rw [ChowPushforwardMap.map_mk, map_mk, ← CycleMaps.embed_eq_pushforward i m, CycleMaps.restrict_embed]

variable [IsClosedImmersion i.left]

theorem intersection (q : ℕ) (a : ProperCycleLinearity.ChowQ X 1) (b : ProperCycleLinearity.ChowQ V q) :
    Divisor.ChowMap.map X m q a (ChowPushforwardMap.map i m m q q rfl b) =
      ChowPushforwardMap.map i m m (1 + q) (1 + q) rfl
        (Divisor.ChowMap.map V m q (map i m a) b) := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X 1 a
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective V q b
  rw [ChowPushforwardMap.map_mk, ← CycleMaps.embed_eq_pushforward i m, map_mk]
  exact divisor i m q a b

end DivisorRestriction

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Chow
