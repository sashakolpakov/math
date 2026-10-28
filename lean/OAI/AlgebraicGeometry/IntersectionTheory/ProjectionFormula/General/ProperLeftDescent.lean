import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.CompatibleMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PairingCongruence
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovedComparison
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowSymmetry

/-! # Proper Left Descent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ProperLeftDescent

noncomputable section

/-! Rationally equivalent original first representatives have the
same intersection class whenever both meet the fixed second cycle
properly. The proof preserves both original pairings while moving. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem equivalent (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a a' : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a a')
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b) (hp' : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a' b) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (p + q) (Supports.ProperCycle.intersectionBilinear X m p q a b) (Supports.ProperCycle.intersectionBilinear X m p q a' b) := by
  obtain ⟨S, hS⟩ := MovedComparison.RelationDescentStrata.exists_data X m p (a - a') ha
  let I := a.support ⊕ a'.support
  let B : I → X.DimensionCycleSupport p := Sum.elim Subtype.val Subtype.val
  have hba := (ChowSymmetry.Graded.meetProperly_comm X p q a b).mp hp
  have hba' := (ChowSymmetry.Graded.meetProperly_comm X p q a' b).mp hp'
  have hfixed : ∀ W ∈ b.support, ∀ i : I, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W.val : Set X.carrier) ∩ ((B i).val : Set X.carrier) → q + p ≤ X.supportCodimension C := by
    intro W hW i C hC
    cases i with
    | inl i => exact hba W hW i.val i.property C hC
    | inr i => exact hba' W hW i.val i.property C hC
  obtain ⟨b', hb', hpos⟩ := CompatibleMoving.cycle X m q p (fun T : S => T.val) B b hfixed
  have hrel := (CompatibleRelations.mem_iff X m q p B b b').mp hb'
  have hstrata : b' ∈ Proper.SupportCycles.submodule X q (fun T : S => T.val) :=
    fun T W hW => hpos (Sum.inl T) W hW
  have hzero := (hS q b' hstrata).2
  rw [map_sub] at hzero
  have hmiddle : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (q + p)
      (Supports.ProperCycle.intersectionBilinear X m q p b' a) (Supports.ProperCycle.intersectionBilinear X m q p b' a') := hzero
  have hleft := Finite.PairingCongruence.equivalent X m q p b b' a
    (fun W hW => hrel.2 (Sum.inl ⟨W, hW⟩))
  have hright := Finite.PairingCongruence.equivalent X m q p b b' a'
    (fun W hW => hrel.2 (Sum.inr ⟨W, hW⟩))
  have hchain := CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X (q + p) hleft
    (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X (q + p) hmiddle (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X (q + p) hright))
  apply (ChowSymmetry.Graded.rationallyEquivalent_cast X (Nat.add_comm p q) _ _).mp
  rw [ChowSymmetry.Graded.bilinear_comm, ChowSymmetry.Graded.bilinear_comm]
  exact hchain

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ProperLeftDescent
