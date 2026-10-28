import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ClopenCycles
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Embedding
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowAssociativity

/-! # Clopen Chow -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ClopenChow

noncomputable section

/-! Restriction and intersection of Chow classes along open and
closed immersions, in all codimensions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection

variable {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left]
  (m : ℕ) [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]

def restrictMap (p : ℕ) : ProperCycleLinearity.ChowQ X p →ₗ[ℚ] ProperCycleLinearity.ChowQ V p :=
  (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p).liftQ ((ProperCycleLinearity.cycleToChowQ V p).comp (Clopen.CycleMaps.restrict i m p)) (by
    intro a ha
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ClopenCycles.restrict_relations i m p ha)

theorem restrictMap_mk (p : ℕ) (a : X.RationalDimensionCycle p) :
    restrictMap i m p (ProperCycleLinearity.cycleToChowQ X p a) = ProperCycleLinearity.cycleToChowQ V p (Clopen.CycleMaps.restrict i m p a) := rfl

theorem restrictMap_push (p : ℕ) (a : ProperCycleLinearity.ChowQ V p) :
    restrictMap i m p (ChowPushforwardMap.map i m m p p rfl a) = a := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective V p a
  rw [ChowPushforwardMap.map_mk, restrictMap_mk, ← Clopen.CycleMaps.embed_eq_pushforward i m, Clopen.CycleMaps.restrict_embed]

variable [IsClosedImmersion i.left]

theorem cycle_intersection (p q : ℕ) (a : X.RationalDimensionCycle p) (b : V.RationalDimensionCycle q) :
    GeneralChowIntersection.chowMap X m p q (ProperCycleLinearity.cycleToChowQ X p a) (ProperCycleLinearity.cycleToChowQ X q (Clopen.CycleMaps.embed i m q b)) =
      ChowPushforwardMap.map i m m (p + q) (p + q) rfl
        (GeneralChowIntersection.chowMap V m p q (ProperCycleLinearity.cycleToChowQ V p (Clopen.CycleMaps.restrict i m p a)) (ProperCycleLinearity.cycleToChowQ V q b)) := by
  obtain ⟨u, hu, hp⟩ := ChowMoving.properly_meeting_representatives X m p q a (Clopen.CycleMaps.embed i m q b)
  have hr : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent V p (Clopen.CycleMaps.restrict i m p a) (Clopen.CycleMaps.restrict i m p u) := by
    change Clopen.CycleMaps.restrict i m p a - Clopen.CycleMaps.restrict i m p u ∈ _
    rw [← map_sub]
    exact ClopenCycles.restrict_relations i m p hu
  have hp' := Clopen.Embedding.meetProperly_restrict i m p q _ _ hp
  rw [Clopen.CycleMaps.restrict_embed] at hp'
  rw [(ProperCycleLinearity.cycleToChowQ_eq_iff X p a u).mpr hu, (ProperCycleLinearity.cycleToChowQ_eq_iff V p _ _).mpr hr,
    ChowAssociativity.mk_proper X m p q _ _ hp,
    ChowAssociativity.mk_proper V m p q _ _ hp', ChowPushforwardMap.map_mk]
  apply congrArg (ProperCycleLinearity.cycleToChowQ X (p + q))
  rw [Clopen.Embedding.intersection_embed i m p q u b hp, Clopen.CycleMaps.embed_eq_pushforward]

theorem intersection (p q : ℕ) (a : ProperCycleLinearity.ChowQ X p) (b : ProperCycleLinearity.ChowQ V q) :
    GeneralChowIntersection.chowMap X m p q a (ChowPushforwardMap.map i m m q q rfl b) =
      ChowPushforwardMap.map i m m (p + q) (p + q) rfl
        (GeneralChowIntersection.chowMap V m p q (restrictMap i m p a) b) := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X p a
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective V q b
  rw [ChowPushforwardMap.map_mk, ← Clopen.CycleMaps.embed_eq_pushforward i m, restrictMap_mk]
  exact cycle_intersection i m p q a b

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ClopenChow
