import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashReturnBounds

/-! The actual preparation and attained-history boundary supply every discarded
word required by the complete accepted-query return. No extra entry-blank
assumption is added to the query caller. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
open BitProgram StructuredCalls HashGreedyRound

theorem accepted_entry_discarded_blank {n m B : ℕ} {initial rows : List (List Bool)}
    (base selected : State 40 896)
    (hr : NativeLeafPreparation.Ready n m B initial base)
    (hupper : ∀ i : Fin 896,
      (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) → base.stacks i = [])
    (hselected : RowBoundary base rows selected) :
    ∀ i, HashMarkedReturn.kept i = false →
      (AcceptedQueryStage.staged selected).stacks i = [] := by
  have hlow : ∀ i : Fin 896, i.val < 768 → selected.stacks i = [] := by
    intro i hi
    have hne (j : Fin 896) (hj : 768 ≤ j.val) : i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      omega
    exact (hselected.frame i (hne 777 (by decide)) (hne 781 (by decide))).trans
      (ready_low hr i hi)
  have hu := rounds_query_workspace base selected rows hselected hupper
  intro i hk
  by_cases h702 : i = 702
  · subst i
    rw [AcceptedQueryStage.staged_702]
    exact hlow 702 (by decide)
  have hout : i ∉ HashMassStaged.stagedPorts := by
    simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil, or_false, not_or]
    simp only [HashMarkedReturn.kept, decide_eq_false_iff_not, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod] at hk
    simp only [Fin.ext_iff, Fin.coe_ofNat_eq_mod] at h702 ⊢
    omega
  have ht : i ≠ 767 := by
    intro h
    subst i
    have hkeep : HashMarkedReturn.kept (767 : Fin 896) = true := by decide
    rw [hkeep] at hk
    cases hk
  rw [AcceptedQueryStage.staged_frame selected i hout ht]
  by_cases hi : i.val < 768
  · exact hlow i hi
  · apply hu i
    simp only [HashMarkedReturn.kept, decide_eq_false_iff_not, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod] at hk
    have hib := i.isLt
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
