import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchBlank
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedNodeFamily

namespace OAI.Algorithms

/-! Exact node streams and reclaimed work tapes at every residual call. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram SubexpLiftRing
noncomputable section
attribute [local irreducible] Execute.guardedModel

variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k initial hg W V L)

theorem prepared_aux_empty (i : Fin 768) (hi : i∈([190,191,699] : List (Fin 768))) :
    (Marked.Wide.maskCopied (Query.prepared p.out)).stacks i=[] := by
  have hn : i≠333 := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> decide
  rw [Marked.Wide.maskCopied_frame _ i hn]
  unfold Query.prepared
  by_cases hp : i∈Count.Prepare.ports
  · exact Query.prepared_count_empty p.out i hp
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl
  · rw [Count.Prepare.output_frame _ 190 hp (by norm_num)]
    simp [Samples.prepared_stacks]
  · rw [Count.Prepare.output_frame _ 191 hp (by norm_num)]
    simp [Samples.prepared_stacks]
  · simp [Count.Prepare.output,BankRoutines.clearBankStacks,hp]

theorem residual_count_empty (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (h323 : a.stacks 323=[]) (h324 : a.stacks 324=[]) :
    (∀i,i∈([190,191,699] : List (Fin 768)) → (Residual.Native.outerReference a).stacks i=[]) ∧
    (∀i,i∈Count.Prepare.ports → (Residual.Native.outerReference a).stacks i=[]) := by
  constructor
  · intro i hi
    have hn : i∉Residual.Branch.mutable ∧ ¬Residual.Native.outerTape i := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl <;> decide
    rw [Residual.Native.outerReference_visible _ _ hn.2,ha.2 i hn.1]
    exact prepared_aux_empty p i hi
  · intro i hi
    have hl := Count.Prepare.ports_lt i hi
    have ho : ¬Residual.Native.outerTape i := by
      intro ho
      simp only [Residual.Native.outerTape] at ho
      rcases ho with rfl|rfl|rfl
      · exact (Count.Prepare.ports_gap 320 (by norm_num) (by norm_num)) hi
      · exact (Count.Prepare.ports_gap 322 (by norm_num) (by norm_num)) hi
      · norm_num [Fin.coe_ofNat_eq_mod] at hl
    rw [Residual.Native.outerReference_visible _ _ ho]
    by_cases h3 : i=323
    · simpa only [h3] using h323
    by_cases h4 : i=324
    · simpa only [h4] using h324
    have hn : i∉Residual.Branch.mutable := by
      simp only [Residual.Branch.mutable,List.mem_cons,List.mem_nil_iff,or_false]
      rintro (he|he|he|he|he|he)
      · exact h3 he
      · exact h4 he
      all_goals subst i; norm_num [Fin.coe_ofNat_eq_mod] at hl
    rw [ha.2 i hn]
    exact query_prepared_count_empty p i hi

theorem invariant_output_node_frame (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (i : Fin 768) (hi : i=256 ∨ i=300) :
    (Residual.Native.outerReference a).stacks i=p.out.stacks i := by
  rcases hi with rfl|rfl
  · rw [Residual.Native.outerReference_visible _ _ (by decide),ha.2 _ (by decide),
      Marked.Wide.maskCopied_frame _ _ (by decide)]
    unfold Query.prepared
    rw [Count.Prepare.output_frame _ _
      (Count.Prepare.protected_not_mem 256 (by simp [Count.Prepare.protectedInputs]))
      (by norm_num), Samples.prepared_frame _ _ (by norm_num) (by norm_num)]
  · rw [Residual.Native.outerReference_visible _ _ (by decide),ha.2 _ (by decide),
      Marked.Wide.maskCopied_frame _ _ (by decide)]
    unfold Query.prepared
    rw [Count.Prepare.output_frame _ _
      (Count.Prepare.protected_not_mem 300 (by simp [Count.Prepare.protectedInputs]))
      (by norm_num), Samples.prepared_frame _ _ (by norm_num) (by norm_num)]

theorem invariant_nodes (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a) :
    ((List.finRange (Query.packingProblem q k hg).Q).map (fun i=>nodeFamily p i.val)).flatten=
      (Residual.Native.outerReference a).stacks 256 := by
  rw [invariant_output_node_frame p a ha 256 (Or.inl rfl)]
  have he : p.out.stacks 256=p.ringState.stacks 256 := p.arithmeticOutput.low 256 (by decide)
  have hQ : (Execute.guardedModel (q.input k) p.lengths).val 21=(Query.packingProblem q k hg).Q :=
    numeric_Q q k p.lengths
  rw [he,p.arithmeticOutput.produced.flatNodes,hQ]
  simp only [LeafRingSetupProgram.nodeWords,List.map_map,Function.comp_def,nodeFamily]
  rfl

theorem invariant_node_source (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (rh : Fin 4 → Bool) (high : List Bool) :
    (Samples.prepared (LeafHighContextProgram.finished (Residual.Native.outerReference a) rh high)).stacks 300=
      Encoding.encodeList id (LeafNodeSamplesProgram.records
        (LeafNodeSamplesProgram.Rel.nodeSamples (nodeFamily p)) 0 (Query.packingProblem q k hg).Q) := by
  rw [Samples.prepared_frame _ 300 (by decide) (by decide),
    LeafHighContextProgram.finished_frame _ _ _ 300 (by decide),
    invariant_output_node_frame p a ha 300 (Or.inr rfl)]
  have he : p.out.stacks 300=p.ringState.stacks 300 := p.arithmeticOutput.low 300 (by decide)
  have hQ : (Execute.guardedModel (q.input k) p.lengths).val 21=(Query.packingProblem q k hg).Q :=
    numeric_Q q k p.lengths
  rw [he,p.arithmeticOutput.produced.framedNodes,hQ,
    LeafNodeSamplesProgram.records_eq_finRange]
  simp only [LeafRingSetupProgram.nodeWords,List.map_map,Function.comp_def,
    LeafNodeSamplesProgram.Rel.nodeSamples,nodeFamily]
  rfl

theorem residual_collector_empty (h728 : initial.stacks 728=[])
    (hb : ∀i,i∈entryBlankPorts → initial.stacks i=[])
    (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a) :
    (Residual.Native.outerReference a).stacks 265=[] := by
  rw [Residual.Native.outerReference_visible _ _ (by decide),ha.2 _ (by decide)]
  exact (query_prepared_empty p 265 (output_sampler_empty p h728 hb 265 (by decide))).resolve_right (by decide)

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
