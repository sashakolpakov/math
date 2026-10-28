import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ResidualMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.ProperSupportCycles
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDimension

/-! # Chow Moving -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowMoving

/-! The full Chow moving lemma on every smooth projective presentation,
including disconnected sources and codimension zero. It gives totality
of the native Chow intersection relation in all codimensions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  {τ : Type} [Finite τ] (Z : τ → IrreducibleCloseds X.carrier)

include m

theorem positive_generator (p : ℕ) (hp : 1 ≤ p) (W : X.DimensionCycleSupport p) :
    ∃ c : X.RationalDimensionCycle p,
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (Finsupp.single W 1) c ∧ c ∈ Proper.SupportCycles.submodule X p Z := by
  let K := X.supportComponent W.val
  let V := (X.componentVariety K).presentation
  let : SmoothOfRelativeDimension m V.structureMap := Component.Image.component_relativeDimension X m K
  let W' := Component.Image.supportPreimage X K p W (X.support_subset_component W.val)
  obtain ⟨c, hc, hproper⟩ := Integral.ResidualMoving.generator V m p hp
    (Component.ProperSupportCycles.family X K Z) W'
  refine ⟨Component.CycleMaps.embed X K p c, ?_, Component.ProperSupportCycles.embed X K Z p c hproper⟩
  have he := Component.CycleMaps.embed_preserves_relations X m K p hc
  change Component.CycleMaps.embed X K p (Finsupp.single W' 1 - c) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p at he
  rw [map_sub, Component.CycleMaps.embed_single, Component.Image.supportImage_preimage] at he
  exact he

omit [Finite τ] in
theorem zero_mem (a : X.RationalDimensionCycle 0) : a ∈ Proper.SupportCycles.submodule X 0 Z := by
  intro t D _ C hC
  have he := (Supports.codimension_strictAnti X m).antitone
    (show C ≤ Z t from fun x hx => (hC hx).2)
  exact (Nat.zero_add _).symm ▸ he

theorem cycle (p : ℕ) (a : X.RationalDimensionCycle p) :
    ∃ c : X.RationalDimensionCycle p,
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a c ∧ c ∈ Proper.SupportCycles.submodule X p Z := by
  by_cases hp : p = 0
  · subst p
    exact ⟨a, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X 0 a, zero_mem X m Z a⟩
  · exact Proper.SupportCycles.lift_cycle X p (Proper.SupportCycles.submodule X p Z) a
      (fun W _ => positive_generator X m Z p (Nat.pos_of_ne_zero hp) W)

omit Z [Finite τ] in
theorem properly_meeting_representatives (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    ∃ a' : X.RationalDimensionCycle p, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a a' ∧ CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a' b := by
  obtain ⟨a', ha', hproper⟩ := cycle X m (fun B : b.support => B.val.val) p a
  refine ⟨a', ha', ?_⟩
  intro A hA B hB C hC
  have he := hproper ⟨B, hB⟩ A hA C hC
  change p + X.supportCodimension B.val ≤ X.supportCodimension C at he
  rwa [B.property] at he

omit Z [Finite τ] in
theorem intersection_representative_exists (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    ∃ c : X.RationalDimensionCycle (p + q), CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p q a b c := by
  obtain ⟨a', ha', hproper⟩ := properly_meeting_representatives X m p q a b
  obtain ⟨c, hc, _⟩ := Supports.ProperCycle.properIntersection_exists_unique X m p q a' b hproper
  exact ⟨c, a', b, c, ha', CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X q b, hc,
    CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (p + q) c⟩

omit Z [Finite τ] in
theorem chowIntersection_nonempty (p q : ℕ) (a : ProperCycleLinearity.ChowQ X p) (b : ProperCycleLinearity.ChowQ X q) :
    (ProperCycleLinearity.chowIntersection X p q a b).Nonempty := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X p a
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X q b
  obtain ⟨c, hc⟩ := intersection_representative_exists X m p q a b
  exact ⟨ProperCycleLinearity.cycleToChowQ X (p + q) c, a, b, c, rfl, rfl, rfl, hc⟩

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowMoving

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowMoving.GraphTotality

/-! The actual graph-intersection pullback relation is nonempty
in every codimension on arbitrary smooth projective presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (f : X.toOver ⟶ Y.toOver) (m n : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

include m n

theorem representsPullback_exists (p : ℕ) (a : Y.RationalDimensionCycle p) :
    ∃ b : X.RationalDimensionCycle p, P.RepresentsPullback f n p a b := by
  let : SmoothOfRelativeDimension (m + n) P.space.structureMap := ProductDimension.relativeDimension P m n
  obtain ⟨c, hc⟩ := intersection_representative_exists P.space (m + n) n p
    (P.graphCycle f n) (P.secondPullbackCycle p a)
  exact ⟨ProperCycleLinearity.cyclePushforward P.fst (n + p) p c, c, hc, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X p _⟩

theorem chowPullback_nonempty (p : ℕ) (a : ProperCycleLinearity.ChowQ Y p) : (ProperCycleLinearity.chowPullback P f n p a).Nonempty := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective Y p a
  obtain ⟨b, hb⟩ := representsPullback_exists P f m n p a
  exact ⟨ProperCycleLinearity.cycleToChowQ X p b, a, b, rfl, rfl, hb⟩

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowMoving.GraphTotality

end

end OAI
