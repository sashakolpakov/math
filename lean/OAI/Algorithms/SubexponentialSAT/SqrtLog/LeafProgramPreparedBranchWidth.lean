import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchMetadata
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostSetup

namespace OAI.Algorithms

/-! Uniform input width for each actual residual call. The enclosing loop's
three untouched streams are omitted; the live counter is bounded from its
literal one-bit record shape. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
noncomputable section

theorem counter_encoded_length (words : List (List Bool)) (h : ℕ)
    (hs : words.map List.length=List.replicate h 1) :
    (Encoding.encodeList id words).length=4*h+1 := by
  have hl : words.length=h := by
    simpa only [List.length_map,List.length_replicate] using congrArg List.length hs
  have hf : words.flatten.length=h := by
    rw [List.length_flatten,hs]
    simp
  rw [ExecCNFTupleOdometer.encoded_length,hf,hl]
  omega

variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k initial hg W V L)

theorem prepared_width_incoming (hw : ∀i,(initial.stacks i).length ≤ W) :
    ∀i,((Query.prepared p.out).stacks i).length ≤ Query.Width.incomingWidth p := by
  intro i
  have h := Query.eval_width (Query.prepare_eval p.out)
    (W+p.frontSteps+p.packingSteps+p.arithmeticSteps) (p.output_width hw) i
  unfold Query.Width.incomingWidth
  omega

theorem counter_width_incoming :
    4*HighIncidenceProgram.Branches.trueCount q.forward.reverse+1 ≤ Query.Width.incomingWidth p := by
  have hm : p.out.stacks 338=q.forward.reverse := by
    rw [Query.Width.output_mask]
    simp only [LeafQueryFrontend.Query.forward,List.reverse_reverse]
  rw [HighIncidenceProgram.Branches.trueCount,Subexp.PaddedCompletion.trueCount_eq_count]
  unfold Query.Width.incomingWidth
  rw [hm]
  omega

theorem residual_input_width (hw : ∀i,(initial.stacks i).length ≤ W)
    (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (words : List (List Bool))
    (hshape : words.map List.length=
      List.replicate (HighIncidenceProgram.Branches.trueCount q.forward.reverse) 1)
    (hc : a.stacks 330=Encoding.encodeList id words)
    (h331 : a.stacks 331=[]) (h323 : a.stacks 323=[]) (h324 : a.stacks 324=[]) :
    ∀i,¬Residual.Native.outerTape i → (a.stacks i).length ≤ Query.Width.incomingWidth p := by
  intro i hi
  by_cases hm : i∈Residual.Branch.mutable
  · simp only [Residual.Branch.mutable,List.mem_cons,List.mem_nil_iff,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl
    · rw [h323]; simp
    · rw [h324]; simp
    · rw [hc,counter_encoded_length words _ hshape]
      exact counter_width_incoming p
    · rw [h331]; simp
    · exact (hi (by simp [Residual.Native.outerTape])).elim
    · rw [ha.1]; simp
  · have h333 : i≠333 := fun he=>hm (by simp [Residual.Branch.mutable,he])
    rw [ha.2 i hm,Marked.Wide.maskCopied_frame _ i h333]
    exact prepared_width_incoming p hw i

theorem high_finished_width (a : Factor.Data) (U : ℕ)
    (hw : ∀i,(a.stacks i).length ≤ U) (rh : Fin 4 → Bool) (high : List Bool)
    (hh : high.length=HighIncidenceProgram.Restriction.highCount (a.stacks 338)) :
    ∀i,((LeafHighContextProgram.finished a rh high).stacks i).length ≤ U := by
  intro i
  by_cases hi : i∈LeafHighContextProgram.changed
  · simp only [LeafHighContextProgram.changed,List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · rw [LeafHighContextProgram.finished_mask,List.length_reverse]
      exact hw 338
    · rw [LeafHighContextProgram.finished_high,List.length_reverse,
        (HighIncidenceProgram.Restriction.zeroMerge_spec _ _ hh).1]
      exact hw 338
    all_goals rw [LeafHighContextProgram.finished_scratch _ _ _ _ (by decide)]; simp
  · rw [LeafHighContextProgram.finished_frame _ _ _ i hi]
    exact hw i

theorem samples_prepared_width (a : Factor.Data) (U : ℕ)
    (hw : ∀i,(a.stacks i).length ≤ U) :
    ∀i,((Samples.prepared a).stacks i).length ≤ U := by
  intro i
  rw [Samples.prepared_stacks]
  simp only [Function.update_apply]
  split_ifs <;> first | simp | exact hw i

theorem invariant_sampler_width (hw : ∀i,(initial.stacks i).length ≤ W)
    (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (words : List (List Bool))
    (hshape : words.map List.length=
      List.replicate (HighIncidenceProgram.Branches.trueCount q.forward.reverse) 1)
    (hc : a.stacks 330=Encoding.encodeList id words)
    (h331 : a.stacks 331=[]) (h323 : a.stacks 323=[]) (h324 : a.stacks 324=[])
    (rh : Fin 4 → Bool) :
    ∀i,((Samples.prepared (LeafHighContextProgram.finished
      (Residual.Native.outerReference a) rh words.flatten)).stacks i).length ≤ Query.Width.incomingWidth p := by
  apply samples_prepared_width
  apply high_finished_width
  · exact Residual.Native.outerReference_wordBound a _
      (residual_input_width p hw a ha words hshape hc h331 h323 h324)
  · rw [Residual.Native.outerReference_visible a 338 (by decide),invariant_mask p a ha,
      List.length_flatten,hshape]
    simp only [List.sum_replicate,smul_eq_mul,mul_one]

theorem nodes_le_incoming (hw : ∀i,(initial.stacks i).length ≤ W) :
    (Query.packingProblem q k hg).Q ≤ Query.Width.incomingWidth p := by
  let i : Fin (Query.packingProblem q k hg).Q := ⟨0,(Query.packingProblem q k hg).hQ⟩
  have h := (PreparedNodeReady.parked p i).nodes
  have hl := p.output_width hw 733
  rw [h,LeafHeadSetupProgram.unary,List.length_replicate] at hl
  unfold Query.Width.incomingWidth
  exact hl.trans (by omega)

theorem node_word_le_incoming (hw : ∀i,(initial.stacks i).length ≤ W) (i : ℕ) :
    (RingProgram.flat (RingNodeProgram.nodeCode ((numeric q k p.lengths).val 33)
      ((numeric q k p.lengths).val 34) (i+1))).length ≤ Query.Width.incomingWidth p := by
  rw [RingProgram.flat_length]
  have hl := p.output_width hw 280
  have he : p.out.stacks 280=p.ringState.stacks 280 := p.arithmeticOutput.low 280 (by decide)
  rw [he,p.arithmeticOutput.produced.caches.fullZero,
    ←Constants.constantCode_flat,RingProgram.flat_length] at hl
  exact hl.trans (by unfold Query.Width.incomingWidth; omega)

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
