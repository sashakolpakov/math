import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowMoving

/-! # Simultaneous Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.SimultaneousMoving

noncomputable section

/-! General Chow moving can meet finitely many cycles of different
codimensions simultaneously, as needed to compare linear combinations
and finite presentations of rational-equivalence relations. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

theorem family (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] {τ : Type} [Finite τ]
    (q : τ → ℕ) (b : ∀ t, X.RationalDimensionCycle (q t)) (a : X.RationalDimensionCycle p) :
    ∃ a' : X.RationalDimensionCycle p, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a a' ∧
      ∀ t, CycleClass.Thom.IntersectionGeometry.MeetProperly X p (q t) a' (b t) := by
  let I := Σ t : τ, (b t).support
  let Z : I → IrreducibleCloseds X.carrier := fun i => i.2.val.val
  obtain ⟨a', ha', hp⟩ := ChowMoving.cycle X m Z p a
  refine ⟨a', ha', ?_⟩
  intro t A hA B hB C hC
  have he := hp (⟨t, ⟨B, hB⟩⟩ : I) A hA C hC
  change p + X.supportCodimension B.val ≤ X.supportCodimension C at he
  rwa [B.property] at he

theorem pair (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle p) (b c : X.RationalDimensionCycle q) :
    ∃ a' : X.RationalDimensionCycle p, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a a' ∧
      CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a' b ∧ CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a' c := by
  let U := b.support ∪ c.support
  obtain ⟨a', ha', hp⟩ := ChowMoving.cycle X m (fun B : U => B.val.val) p a
  refine ⟨a', ha', ?_, ?_⟩
  · intro A hA B hB C hC
    have he := hp ⟨B, Finset.mem_union_left _ hB⟩ A hA C hC
    change p + X.supportCodimension B.val ≤ X.supportCodimension C at he
    rwa [B.property] at he
  · intro A hA B hB C hC
    have he := hp ⟨B, Finset.mem_union_right _ hB⟩ A hA C hC
    change p + X.supportCodimension B.val ≤ X.supportCodimension C at he
    rwa [B.property] at he

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.SimultaneousMoving
