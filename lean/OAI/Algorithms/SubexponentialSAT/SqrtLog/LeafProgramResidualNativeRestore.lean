import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeSamples

namespace OAI.Algorithms

/-! Exact tape restoration for repeated residual calls. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls
open LeafNodeSamplesProgram

attribute [local irreducible] Count.Prepare.ports

noncomputable section

theorem high_stacks (a : Data) (regs : Fin 4 → Bool) (high : List Bool)
    (he : ∀ i∈LeafHighContextProgram.changed,a.stacks i=[]) :
    (LeafHighContextProgram.finished a regs high).stacks=
      Function.update (Function.update a.stacks 702 (a.stacks 338).reverse) 703
        (HighIncidenceProgram.Restriction.zeroMerge (a.stacks 338) high).reverse := by
  funext i
  by_cases h702 : i=702
  · subst i; simp
  by_cases h703 : i=703
  · subst i; simp
  simp only [Function.update_of_ne h702,Function.update_of_ne h703]
  by_cases hs : i∈LeafHighContextProgram.scratch
  · rw [LeafHighContextProgram.finished_scratch a regs high i hs]
    symm
    apply he i
    simpa only [LeafHighContextProgram.changed,LeafHighContextProgram.scratch,
      List.mem_cons,List.mem_nil_iff,or_false,h702,h703,false_or] using hs
  · apply LeafHighContextProgram.finished_frame
    simpa only [LeafHighContextProgram.changed,LeafHighContextProgram.scratch,
      List.mem_cons,List.mem_nil_iff,or_false,h702,h703,false_or] using hs

theorem collector_final_stacks (a : Data) (nodes : ℕ → List Bool) {Q : ℕ}
    (jets : Fin Q → List Bool)
    (he : ∀ i∈collectorBlankPorts,a.stacks i=[]) :
    tapes (Rel.finishedIndexed a.stacks nodes jets)=
      Function.update (Function.update a.stacks 256
        ((List.finRange Q).map (fun i => nodes i.val)).flatten) 265
        ((List.finRange Q).map jets).flatten := by
  funext i
  by_cases h256 : i=256
  · subst i; simp [Rel.finishedIndexed]
  by_cases h265 : i=265
  · subst i; simp [Rel.finishedIndexed]
  simp only [Function.update_of_ne h256,Function.update_of_ne h265]
  by_cases hb : i∈collectorBlankPorts
  · have hz := he i hb
    simp only [collectorBlankPorts,List.mem_cons,List.mem_nil_iff,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact False.elim (h265 rfl)
    all_goals simpa [tapes,Rel.finishedIndexed] using hz.symm
  · apply collector_frame
    simpa [collectorPorts,collectorBlankPorts,h256] using hb

theorem sample_prepare_stacks (a : Data) (h190 : a.stacks 190=[]) (h191 : a.stacks 191=[]) :
    (Samples.prepared a).stacks=a.stacks := by
  rw [Samples.prepared_stacks]
  funext i
  by_cases h : i=190
  · subst i; simp [h190]
  by_cases h' : i=191
  · subst i; simp [h191]
  simp [h,h']

theorem count_prepare_stacks (a : Data)
    (he : ∀ i∈Count.Prepare.ports,a.stacks i=[]) (h699 : a.stacks 699=[]) :
    (Count.Prepare.output a).stacks=a.stacks := by
  funext i
  by_cases hm : i∈Count.Prepare.ports
  · change BankRoutines.clearBankStacks Count.Prepare.ports _ i=a.stacks i
    rw [BankRoutines.clearBankStacks_mem _ _ _ hm,he i hm]
  · by_cases hs : i=699
    · subst i
      simp [Count.Prepare.output,BankRoutines.clearBankStacks,hm,h699]
    · exact Count.Prepare.output_frame a i hm hs

end
end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
