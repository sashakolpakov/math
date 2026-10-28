import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemanticsEnumeration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramLoop

namespace OAI.Algorithms

/-! High-mask coordinates have empty fibers in the actual emitted records. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open PackingIncidenceInput

theorem fiberIndices_eq_nil_of_absent (query : ℕ) (ps : List (ℕ × ℕ))
    (h : ∀ p ∈ ps, p.1 ≠ query) :
    ∀ index, LayoutOwnerFiberProgram.fiberIndices query index ps = [] := by
  induction ps with
  | nil => intros; rfl
  | cons p ps ih =>
    intro index
    have hp := h p (by simp)
    have ht : ∀ q ∈ ps, q.1 ≠ query := by
      intro q hq
      exact h q (List.mem_cons_of_mem _ hq)
    simpa only [LayoutOwnerFiberProgram.fiberIndices, ite_eq_right hp] using ih ht (index+1)

theorem native_high_fiber_empty (scopes : List (List ℕ)) (mask : List Bool)
    (u : Fin mask.length) (hu : mask.get u = true) (index : ℕ) :
    LayoutOwnerFiberProgram.fiberIndices u.val index
      (Semantics.nativeEntries scopes mask) = [] := by
  apply fiberIndices_eq_nil_of_absent
  intro p hp he
  rcases p with ⟨v,e⟩
  change v = u.val at he
  subst v
  exact native_no_high_owner scopes mask u hu e hp

theorem native_high_address_fiber_empty (scopes : List (List ℕ)) (mask : List Bool)
    (u : Fin mask.length) (hu : mask.get u = true) (offset index : ℕ) :
    LayoutOwnerFiberProgram.fiberIndices u.val index
      ((Semantics.nativeEntries scopes mask).map fun p => (p.1,offset+p.2)) = [] := by
  apply fiberIndices_eq_nil_of_absent
  intro p hp he
  obtain ⟨⟨v,e⟩, hm, rfl⟩ := List.mem_map.mp hp
  change v = u.val at he
  subst v
  exact native_no_high_owner scopes mask u hu e hm

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
