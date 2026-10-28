import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ClosedComponents
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.TripleCycles

/-! # Triple Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.TripleMoving

noncomputable section

/-! Moving against all geometric components of pairwise intersections
places three finite cycles in proper triple position. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.TripleCycles

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q t : ℕ) [SmoothOfRelativeDimension m X.structureMap]

include m

theorem first (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle t) (hbc : CycleClass.Thom.IntersectionGeometry.MeetProperly X q t b c) :
    ∃ a' : X.RationalDimensionCycle p, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a a' ∧
      CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a' b ∧ CycleClass.Thom.IntersectionGeometry.MeetProperly X p t a' c ∧ Proper.TripleCycles.MeetTriply X p q t a' b c := by
  let S (B : X.DimensionCycleSupport q) (D : X.DimensionCycleSupport t) : Closeds X.carrier :=
    ⟨(B.val : Set X.carrier) ∩ D.val, B.val.isClosed.inter D.val.isClosed⟩
  let F (B : X.DimensionCycleSupport q) (D : X.DimensionCycleSupport t) :=
    Finite.ClosedComponents.components X.carrier (S B D)
  let I := b.support ⊕ (c.support ⊕ (Σ B : b.support, Σ D : c.support, F B.val D.val))
  let Z : I → IrreducibleCloseds X.carrier := fun i =>
    match i with
    | Sum.inl B => B.val.val
    | Sum.inr (Sum.inl D) => D.val.val
    | Sum.inr (Sum.inr i) => i.2.2.val
  obtain ⟨a', ha, hp⟩ := ChowMoving.cycle X m Z p a
  refine ⟨a', ha, ?_, ?_, ?_⟩
  · intro A hA B hB E hE
    have he := hp (Sum.inl ⟨B, hB⟩) A hA E hE
    change p + X.supportCodimension B.val ≤ X.supportCodimension E at he
    rwa [B.property] at he
  · intro A hA D hD E hE
    have he := hp (Sum.inr (Sum.inl ⟨D, hD⟩)) A hA E hE
    change p + X.supportCodimension D.val ≤ X.supportCodimension E at he
    rwa [D.property] at he
  · intro A hA B hB D hD E hE
    obtain ⟨W, hW⟩ := Supports.closedComponentSupport_covers X.carrier (S B D) E
      (fun x hx => ⟨(hE hx).1.2, (hE hx).2⟩)
    let V := CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier (S B D) W
    have hV : V ∈ F B D := (Finite.ClosedComponents.mem_iff X.carrier (S B D) V).mpr ⟨W, rfl⟩
    have hv := hp (Sum.inr (Sum.inr ⟨⟨B, hB⟩, ⟨D, hD⟩, ⟨V, hV⟩⟩)) A hA E
      (fun x hx => ⟨(hE hx).1.1, hW hx⟩)
    change p + X.supportCodimension V ≤ X.supportCodimension E at hv
    have hw := hbc B hB D hD V (Finite.ClosedComponents.subset X.carrier (S B D) V hV)
    omega

theorem representatives (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle t) :
    ∃ a' : X.RationalDimensionCycle p, ∃ b' : X.RationalDimensionCycle q,
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a a' ∧ CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X q b b' ∧
      CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a' b' ∧ CycleClass.Thom.IntersectionGeometry.MeetProperly X p t a' c ∧
      CycleClass.Thom.IntersectionGeometry.MeetProperly X q t b' c ∧ Proper.TripleCycles.MeetTriply X p q t a' b' c := by
  obtain ⟨b', hb, hbc⟩ := ChowMoving.properly_meeting_representatives X m q t b c
  obtain ⟨a', ha, hab, hac, ht⟩ := first X m p q t a b' c hbc
  exact ⟨a', b', ha, hb, hab, hac, hbc, ht⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.TripleMoving
