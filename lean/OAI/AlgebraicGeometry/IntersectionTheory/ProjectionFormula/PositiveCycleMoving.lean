import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.SupportAvoidance
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentCycleSeparation

/-! # Positive Cycle Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycleMoving

noncomputable section

/-! Cycles of any positive codimension can be rationally moved so that no
component is contained in any of finitely many positive-codimension supports. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m r q : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] (hq : 0 < q)

include m hq

theorem move_single (S : Finset (X.DimensionCycleSupport q)) (C : X.DimensionCycleSupport (r + 1)) :
    ∃ b : X.RationalDimensionCycle (r + 1), CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (r + 1) (Finsupp.single C 1) b ∧
      ∀ B ∈ b.support, ∀ D ∈ S, ¬ B.val ≤ D.val := by
  by_cases hC : ∃ D ∈ S, C.val ≤ D.val
  · obtain ⟨D, hD, hCD⟩ := hC
    obtain ⟨A, hCA, hA⟩ := Finite.SupportAvoidance.exists_support X m r q hq C S
    let Z (B : S) : Closeds X.carrier :=
      ⟨(A.val : Set X.carrier) ∩ B.val.val, A.val.isClosed.inter B.val.val.isClosed⟩
    have hp (B : S) (E : IrreducibleCloseds X.carrier) (hE : (E : Set X.carrier) ⊆ Z B) :
        r + 1 ≤ X.supportCodimension E := by
      have hEA : E ≤ A.val := fun _ hx => (hE hx).1
      have hn : E ≠ A.val := by
        intro he
        exact hA B.val B.property (fun x hx => (hE (he ▸ hx)).2)
      have hh := Supports.codimension_strictAnti X m (lt_of_le_of_ne hEA hn)
      rw [A.property] at hh
      omega
    have hf (B : S) := Supports.finite_supports_in_proper_closed X m (r + 1) (Z B) (hp B)
    let T := Finset.univ.biUnion (fun B : S => (hf B).toFinset)
    have hmem (E : X.DimensionCycleSupport (r + 1)) (B : S) (hEA : E.val ≤ A.val)
        (hEB : E.val ≤ B.val.val) : E ∈ T := by
      apply Finset.mem_biUnion.mpr
      refine ⟨B, Finset.mem_univ _, ?_⟩
      apply (hf B).mem_toFinset.mpr
      have he := E.val.isIrreducible.isGenericPoint_genericPoint E.val.isClosed
      exact ⟨hEA he.mem, hEB he.mem⟩
    obtain ⟨d, hd, hs, he⟩ := AdjacentCycleSeparation.exists_relation X m r A T C
      (hmem C ⟨D, hD⟩ hCA hCD) hCA
    refine ⟨Finsupp.single C 1 - d, ?_, ?_⟩
    · change Finsupp.single C 1 - (Finsupp.single C 1 - d) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (r + 1)
      rwa [sub_sub_cancel]
    · intro B hB E hE hBE
      apply Finsupp.mem_support_iff.mp hB
      by_cases hBC : B = C
      · subst B
        rw [Finsupp.sub_apply, Finsupp.single_eq_same, he C (hmem C ⟨D, hD⟩ hCA hCD), ite_eq_left rfl, sub_self]
      · rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hBC]
        by_cases hBA : B.val ≤ A.val
        · rw [he B (hmem B ⟨E, hE⟩ hBA hBE), ite_eq_right hBC, sub_self]
        · have hd0 : d B = 0 := by
            by_contra hn
            exact hBA (hs B (Finsupp.mem_support_iff.mpr hn))
          rw [hd0, sub_self]
  · refine ⟨Finsupp.single C 1, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (r + 1) _, ?_⟩
    intro B hB D hD hBD
    have he : B = C := by simpa using hB
    subst B
    exact hC ⟨D, hD, hBD⟩

theorem move (S : Finset (X.DimensionCycleSupport q)) (a : X.RationalDimensionCycle (r + 1)) :
    ∃ b : X.RationalDimensionCycle (r + 1), CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (r + 1) a b ∧
      ∀ B ∈ b.support, ∀ D ∈ S, ¬ B.val ≤ D.val := by
  induction a using Finsupp.induction_linear with
  | zero =>
    refine ⟨0, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (r + 1) 0, ?_⟩
    intro B hB
    simp at hB
  | add a b ha hb =>
    obtain ⟨a', ha', hsa⟩ := ha
    obtain ⟨b', hb', hsb⟩ := hb
    refine ⟨a' + b', ?_, ?_⟩
    · change (a + b) - (a' + b') ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (r + 1)
      have he : (a + b) - (a' + b') = (a - a') + (b - b') := by abel
      rw [he]
      exact Submodule.add_mem _ ha' hb'
    · intro B hB D hD
      rcases Finset.mem_union.mp (Finsupp.support_add hB) with hB | hB
      · exact hsa B hB D hD
      · exact hsb B hB D hD
  | single C t =>
    obtain ⟨b, hb, hs⟩ := move_single X m r q hq S C
    refine ⟨t • b, ?_, fun B hB D hD => hs B (Finsupp.support_smul hB) D hD⟩
    change Finsupp.single C t - t • b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (r + 1)
    have hr : Finsupp.single C t = t • Finsupp.single C (1 : ℚ) := by simp
    rw [hr, ← smul_sub]
    exact Submodule.smul_mem _ t hb

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycleMoving
