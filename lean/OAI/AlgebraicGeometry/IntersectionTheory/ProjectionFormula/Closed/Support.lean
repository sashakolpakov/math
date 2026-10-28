import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleLinearExpansion
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowAssociativity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.EmbeddingCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardComposition

/-! # Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.Support

noncomputable section

/-! Intersection with a cycle supported on a closed immersion remains
in its pushforward image. A section retraction recovers that class. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.EmbeddingCycle.Maps

theorem support (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (a : X.RationalDimensionCycle p)
    (b : X.RationalDimensionCycle q) (h : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b)
    (S : Set X.carrier) (hb : ∀ B ∈ b.support, (B.val : Set X.carrier) ⊆ S)
    (C : X.DimensionCycleSupport (p + q)) (hC : C ∈ (Supports.ProperCycle.intersectionBilinear X m p q a b).support) :
    (C.val : Set X.carrier) ⊆ S := by
  obtain ⟨A, hA, B, hB, hc⟩ := CycleLinearExpansion.support X m p q a b C hC
  have hn := Finsupp.mem_support_iff.mp hc
  rw [Supports.ProperCycle.pairCycle_apply X m p q A B (h A hA B hB)] at hn
  have hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (B.val : Set X.carrier) := by
    by_contra hx
    exact hn (dite_eq_right (fun h => hx h.2))
  exact ((Supports.supportPoint_mem_iff_subset
    (⟨(B.val : Set X.carrier), B.val.isClosed⟩ : Closeds X.carrier) C.val).mp hx).trans (hb B hB)

variable {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (i : V.toOver ⟶ X.toOver) [IsClosedImmersion i.left]
  (n m r : ℕ) [SmoothOfRelativeDimension n V.structureMap] [SmoothOfRelativeDimension m X.structureMap]
  (hd : n + r = m) (p q : ℕ)

include hd in
theorem image (a : ProperCycleLinearity.ChowQ X p) (b : ProperCycleLinearity.ChowQ V q) :
    ∃ c : ProperCycleLinearity.ChowQ V (p + q), ChowPushforwardMap.map i n m (p + q) (p + (q + r)) (by omega) c =
      General.GeneralChowIntersection.chowMap X m p (q + r) a
        (ChowPushforwardMap.map i n m q (q + r) (by omega) b) := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X p a
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective V q b
  let b' := ProperCycleLinearity.cyclePushforward i q (q + r) b
  obtain ⟨a', ha, hp⟩ := General.ChowMoving.properly_meeting_representatives X m p (q + r) a b'
  let c := Supports.ProperCycle.intersectionBilinear X m p (q + r) a' b'
  have hb : ∀ B ∈ b'.support, (B.val : Set X.carrier) ⊆ Set.range i.left := by
    intro B hB
    have he := EmbeddingCycle.Maps.embed_eq_pushforward i n m q (q + r) (by omega)
    change B ∈ (ProperCycleLinearity.cyclePushforward i q (q + r) b).support at hB
    rw [← he] at hB
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hB)
    change (ProperCycleLinearity.imageSupport i D.val : Set X.carrier) ⊆ Set.range i.left
    rw [ProperCycleLinearity.imageSupport_eq_image]
    exact Set.image_subset_range _ _
  have hc := Support.support X m p (q + r) a' b' hp (Set.range i.left) hb
  refine ⟨ProperCycleLinearity.cycleToChowQ V (p + q) (EmbeddingCycle.Maps.restrict i n m (p + q) (p + (q + r)) (by omega) c), ?_⟩
  rw [ChowPushforwardMap.map_mk, ← EmbeddingCycle.Maps.embed_eq_pushforward i n m (p + q) (p + (q + r)) (by omega),
    EmbeddingCycle.Maps.embed_restrict i n m (p + q) (p + (q + r)) (by omega) c hc,
    ChowPushforwardMap.map_mk, (ProperCycleLinearity.cycleToChowQ_eq_iff X p a a').mpr ha]
  exact (General.ChowAssociativity.mk_proper X m p (q + r) a' b' hp).symm

theorem pushforward_id (Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k t : ℕ)
    [SmoothOfRelativeDimension k Y.structureMap] (a : ProperCycleLinearity.ChowQ Y t) :
    ChowPushforwardMap.map (𝟙 Y.toOver) k k t t rfl a = a := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective Y t a
  rw [ChowPushforwardMap.map_mk, ProperCycleLinearity.cyclePushforward_id]
  rfl

include hd in
theorem reconstruct (f : X.toOver ⟶ V.toOver) (hf : i ≫ f = 𝟙 V.toOver)
    (a : ProperCycleLinearity.ChowQ X p) (b : ProperCycleLinearity.ChowQ V q) :
    ChowPushforwardMap.map i n m (p + q) (p + (q + r)) (by omega)
      (ChowPushforwardMap.map f m n (p + (q + r)) (p + q) (by omega)
        (General.GeneralChowIntersection.chowMap X m p (q + r) a
          (ChowPushforwardMap.map i n m q (q + r) (by omega) b))) =
      General.GeneralChowIntersection.chowMap X m p (q + r) a
        (ChowPushforwardMap.map i n m q (q + r) (by omega) b) := by
  obtain ⟨c, hc⟩ := image i n m r hd p q a b
  rw [← hc, ChowPushforwardComposition.comp i f n m n (p + q) (p + (q + r)) (p + q)
    (by omega) (by omega) rfl c, hf, pushforward_id]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.Support
