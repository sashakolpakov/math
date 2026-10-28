import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.Sets.Opens
import Mathlib.Data.Fintype.EquivFin

/-! # Compact Shrinking Cover -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CompactShrinkingCover

noncomputable section

/-!
# Finite shrinking refinements of compact Hausdorff open covers

The finite refinement is constructed from compactness followed by mathlib's
shrinking lemma. Its index set is `Fin n`, including `Fin 0` when appropriate.
Every closure containment refers to the actual topological closure in `X`.
-/

open Set _root_.TopologicalSpace

variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Every open cover of a compact Hausdorff space has a finite open shrinking
refinement. Each new set has its closure inside its assigned original set. -/
theorem exists_finite_shrinking_cover (U : ι → Opens X) (hU : iSup U = ⊤) :
    ∃ (n : ℕ) (r : Fin n → ι) (V : Fin n → Opens X),
      iSup V = ⊤ ∧ ∀ j, closure (V j : Set X) ⊆ (U (r j) : Set X) := by
  classical
  have hcoverSet : (⋃ i, (U i : Set X)) = univ := by
    rw [← Opens.coe_iSup, hU, Opens.coe_top]
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (U i : Set X)) (fun i => (U i).isOpen) hcoverSet.ge
  let n := Fintype.card s
  let e : Fin n ≃ s := (Fintype.equivFin s).symm
  let r : Fin n → ι := fun j => (e j).1
  have hfiniteCover : (⋃ j, (U (r j) : Set X)) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨i, hi⟩, ?_⟩
    simpa only [r, Equiv.apply_symm_apply] using hxi
  obtain ⟨V, hcover, hopen, hsub⟩ := exists_iUnion_eq_closure_subset
    (fun j => (U (r j)).isOpen) (fun _ => Set.toFinite _) hfiniteCover
  refine ⟨n, r, fun j => ⟨V j, hopen j⟩, ?_, hsub⟩
  apply Opens.ext
  simpa only [Opens.coe_iSup, Opens.coe_top, Opens.coe_mk] using hcover

end

end OAI.AlgebraicTopology.DeRham.Comparison.CompactShrinkingCover
