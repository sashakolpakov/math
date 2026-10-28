import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchMetadata
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryResidualBlank

namespace OAI.Algorithms

/-! The sampler and reconstruction start in the blank workspace produced by
the actual query setup. These facts are preserved by the branch invariant. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
noncomputable section

variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k initial hg W V L)

def entryBlankPorts : List (Fin 768) :=
  Residual.Native.collectorBlankPorts ++ LeafHighContextProgram.changed

theorem output_sampler_empty (h728 : initial.stacks 728=[])
    (he : ∀i,i∈entryBlankPorts → initial.stacks i=[]) :
    ∀i,i∈Residual.Native.collectorBlankPorts → p.out.stacks i=[] := by
  intro i hi
  have hinit : initial.stacks i=[] := he i (List.mem_append_left _ hi)
  by_cases hr : LeafRingSetupProgram.ResidualFrame.residualTape i
  · exact p.residual_empty h728 i hr hinit
  have hsmall : i=78 ∨ i=102 ∨ i=104 := by
    simp only [Residual.Native.collectorBlankPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
    simp only [LeafRingSetupProgram.ResidualFrame.residualTape,List.mem_cons,List.mem_nil_iff,or_false] at hr
    tauto
  rcases hsmall with rfl|rfl|rfl
  all_goals
    apply p.arithmeticOutput.lowBlank _ (by decide)
    rw [p.packingFrame _ (by decide) (by decide) (by decide)]
    rw [p.frontOutput.frame _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)]
    exact hinit

theorem output_high_empty
    (he : ∀i,i∈entryBlankPorts → initial.stacks i=[]) :
    ∀i,i∈LeafHighContextProgram.changed → p.out.stacks i=[] := by
  intro i hi
  have hinit : initial.stacks i=[] := he i (List.mem_append_right _ hi)
  simp only [LeafHighContextProgram.changed,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    rw [p.arithmeticOutput.highFrame _ (by decide) (by decide) (by decide),
      p.packingFrame _ (by decide) (by decide) (by decide)]
    rw [p.frontOutput.frame _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)]
    exact hinit

theorem query_prepared_empty (i : Fin 768) (he : p.out.stacks i=[]) :
    (Marked.Wide.maskCopied (Query.prepared p.out)).stacks i=[] ∨ i=333 := by
  by_cases hi : i=333
  · exact Or.inr hi
  left
  rw [Marked.Wide.maskCopied_frame _ i hi]
  by_cases hc : i∈Count.Prepare.ports
  · exact Query.prepared_count_empty _ _ hc
  unfold Query.prepared
  by_cases ht : i=699
  · subst i
    simp [Count.Prepare.output,BankRoutines.clearBankStacks,hc]
  rw [Count.Prepare.output_frame _ i hc ht]
  by_cases h0 : i=190
  · subst i; simp [Samples.prepared_stacks]
  by_cases h1 : i=191
  · subst i; simp [Samples.prepared_stacks]
  exact (Samples.prepared_frame _ i h0 h1).trans he

theorem query_prepared_count_empty (i : Fin 768) (hi : i∈Count.Prepare.ports) :
    (Marked.Wide.maskCopied (Query.prepared p.out)).stacks i=[] := by
  have h333 : i≠333 := by
    have h := Count.Prepare.ports_lt i hi
    intro he; subst i; norm_num [Fin.coe_ofNat_eq_mod] at h
  rw [Marked.Wide.maskCopied_frame _ i h333]
  exact Query.prepared_count_empty _ _ hi

theorem invariant_entry_empty (h728 : initial.stacks 728=[])
    (he : ∀i,i∈entryBlankPorts → initial.stacks i=[])
    (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a) :
    (∀i,i∈LeafHighContextProgram.changed → (Residual.Native.outerReference a).stacks i=[]) ∧
    (∀rh high i,i∈Residual.Native.collectorBlankPorts →
      (Samples.prepared (LeafHighContextProgram.finished (Residual.Native.outerReference a) rh high)).stacks i=[]) := by
  have hhigh : ∀i,i∈LeafHighContextProgram.changed → (Residual.Native.outerReference a).stacks i=[] := by
    intro i hi
    have hn : i∉Residual.Branch.mutable := by
      simp only [LeafHighContextProgram.changed,List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have ho : ¬Residual.Native.outerTape i := by
      simp only [LeafHighContextProgram.changed,List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    rw [Residual.Native.outerReference_visible a i ho,ha.2 i hn]
    exact (query_prepared_empty p i (output_high_empty p he i hi)).resolve_right
      (fun he=>hn (by simp [Residual.Branch.mutable,he]))
  refine ⟨hhigh,?_⟩
  intro rh high i hi
  have hf : i∉LeafHighContextProgram.changed ∧ i∉Residual.Branch.mutable ∧
      ¬Residual.Native.outerTape i ∧ i≠190 ∧ i≠191 := by
    simp only [Residual.Native.collectorBlankPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  rw [Samples.prepared_frame _ i hf.2.2.2.1 hf.2.2.2.2,
    LeafHighContextProgram.finished_frame _ rh high i hf.1,
    Residual.Native.outerReference_visible a i hf.2.2.1,ha.2 i hf.2.1]
  exact (query_prepared_empty p i (output_sampler_empty p h728 he i hi)).resolve_right
    (fun he=>hf.2.1 (by simp [Residual.Branch.mutable,he]))

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
