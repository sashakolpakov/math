import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchCount
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram

/-! The actual current-high decoder, kept independent of the complete query
and high-loop composition so the fixed stream can consume its proved run. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount
open HashGreedyProgram.NativeRound

abbrev Data := State 40 896

/-- Actual entry of the fixed conditioned stream. Cleanup is charged only
on its eight touched words, and decoding uses the physical current counter
and current descending mask. The output restores the original compact cap. -/
theorem prepare_high_resources {n : ℕ} (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1)
    (rank : Fin (2^H.card)) (hrank : CounterPrograms.value words.flatten=rank.val)
    (a : Data) (P B : ℕ)
    (hc : a.stacks 330=Encoding.encodeList id words)
    (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (hcounter : (a.stacks 330).length≤P) (hmask : (a.stacks 338).length≤P)
    (hchanged : ∀ i∈highChanged,(a.stacks i).length≤P)
    (hB : ∀ i,(a.stacks i).length≤B) :
    ∃ steps rf, let b := highResult (resetHighState a) rf words.flatten
      Eval prepareHigh steps a b ∧ steps≤18*P+65*n+67 ∧
      b.stacks 702=List.ofFn (fun v : Fin n => decide (v∈H)) ∧
      b.stacks 703=List.ofFn (HighIncidence.glue H
        (SqrtLog.HighIncidenceProgram.Rank.highEquiv
          (SqrtLog.HighIncidenceProgram.Order.highOrder H) rank) (fun _ => false)) ∧
      (∀ i,i∉highChanged → b.stacks i=a.stacks i) ∧
      (∀ i,(b.stacks i).length≤B) ∧
      StageSpace prepareHigh (steps+1) a (max (67*P+37) B) := by
  have hmaskLength : (a.stacks 338).length=n := by
    rw [hm]
    simp [HighIncidenceProgram.descendingHighMask,SqrtLog.HighIncidenceProgram.Order.coordinates]
  have hcount : H.card=SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 338) := by
    rw [hm]
    exact (PreparedBranchCount.descendingMask_count H).symm
  have hmr := resetHigh_frame a 338 (by decide)
  have hcr := resetHigh_frame a 330 (by decide)
  have hresetBound : ∀ i,((resetHighState a).stacks i).length≤B := by
    intro i
    by_cases hi : i∈highChanged
    · simp [resetHighState,BankRoutines.clearBankStacks,hi]
    · rw [resetHigh_frame a i hi]
      exact hB i
  obtain ⟨localSteps,rf,ht,he⟩ := high_eval (resetHighState a) words H.card
    (hcr.trans hc) (fun i hi => BankRoutines.clearBankStacks_mem i highChanged a.stacks hi)
    hshape (by rw [hmr]; exact hcount)
  have hsum : (highChanged.map
      (fun i => ((StackRoutines.clearStacks 702 a.stacks) i).length)).sum≤8*P := by
    have hb : ∀ i∈highChanged,((StackRoutines.clearStacks 702 a.stacks) i).length≤P := by
      intro i hi
      by_cases hz : i=702
      · subst i
        simp [StackRoutines.clearStacks]
      · simpa only [StackRoutines.clearStacks,Function.update_of_ne hz] using hchanged i hi
    have hh := List.sum_le_length_nsmul
      (highChanged.map (fun i => ((StackRoutines.clearStacks 702 a.stacks) i).length)) P
      (by intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact hb i hi)
    simpa only [List.length_map,show highChanged.length=8 from rfl,smul_eq_mul] using hh
  have hresetTime : resetHighCost a≤18*P+30 := by
    have ht := hchanged 702 (by decide)
    unfold resetHighCost
    omega
  have hdim : H.card≤n := by simpa using Finset.card_le_univ H
  have htime : resetHighCost a+localSteps≤18*P+65*n+67 := by
    rw [hmr,hmaskLength] at ht
    omega
  have whole := (resetHigh_eval a).seq he
  obtain ⟨prefixSteps,otherRegs,htrace,_,hprefix⟩ := HighBranchSpace.prepare_high_space
    a words H.card P (max (67*P+37) B) 778 777 hc hshape hcount hcounter hmask
    (Nat.le_max_left _ _)
    (fun i => (hB i).trans (Nat.le_max_right _ _))
  have hsame : prefixSteps=resetHighCost a+localSteps+1 :=
    StreamResources.halted_trace_steps_eq htrace (compiled_halt_trace whole 778 777) rfl rfl
  refine ⟨_,rf,whole,htime,?_,?_,?_,?_,?_⟩
  · rw [highResult_mask,hmr,hm]
    change (PreparedBranchCount.descendingMask H).reverse=_
    rw [PreparedBranchCount.descendingMask_eq,List.reverse_reverse]
  · rw [highResult_bits,hmr,hm]
    exact HighBranchSpace.rank_high_vector_semantics H words hshape rank hrank
  · intro i hi
    exact (highResult_frame _ rf words.flatten i hi).trans (resetHigh_frame a i hi)
  · apply HighBranchSpace.result_bound _ rf words.flatten B _ hresetBound
    rw [PreparedBranchCount.flattened_length H words hshape,hmr]
    exact hcount
  · constructor
    simpa only [hsame] using hprefix

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
