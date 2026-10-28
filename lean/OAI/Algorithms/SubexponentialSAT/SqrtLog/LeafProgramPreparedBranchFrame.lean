import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualBranchFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeOuter

namespace OAI.Algorithms

/-! The actual branch invariant supplies the collector's static frame. The
counter and accumulator cells are explicitly excluded; no equality of their
variable-size contents is used. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod
noncomputable section

private def OffControl (a b : Factor.Data) : Prop :=
  ∀i,i∉PreparedNodeReady.branchControlPorts → a.stacks i=b.stacks i

private theorem invariant_offControl {base a : Factor.Data}
    (ha : Residual.Branch.Invariant base a) : OffControl a base := by
  intro i hi
  apply ha.2 i
  simp only [Residual.Branch.mutable,PreparedNodeReady.branchControlPorts,
    List.mem_cons,List.mem_nil_iff,or_false] at *
  tauto

private theorem outer_offControl (a : Factor.Data) : OffControl (Residual.Native.outerReference a) a := by
  intro i hi
  apply Residual.Native.outerReference_visible
  intro ht
  apply hi
  simp only [Residual.Native.outerTape] at ht
  rcases ht with rfl|rfl|rfl <;> decide

private theorem counter_offControl (a : Factor.Data) (counter : List Bool) :
    OffControl a ⟨a.regs,Function.update a.stacks 330 counter⟩ := by
  intro i hi
  have hn : i≠330 := fun h=>hi (by simp [PreparedNodeReady.branchControlPorts,h])
  exact (Function.update_of_ne hn counter a.stacks).symm

private theorem high_offControl {a b : Factor.Data} (hf : OffControl a b)
    (regs : Fin 4 → Bool) (high : List Bool) :
    OffControl (LeafHighContextProgram.finished a regs high)
      (LeafHighContextProgram.finished b regs high) := by
  intro i hi
  have hm := hf 338 (by decide)
  by_cases hc : i∈LeafHighContextProgram.changed
  · simp only [LeafHighContextProgram.changed,List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simp only [LeafHighContextProgram.finished_mask,hm]
    · simp only [LeafHighContextProgram.finished_high,hm]
    all_goals
      apply Eq.trans (LeafHighContextProgram.finished_scratch a regs high _ (by decide))
      exact (LeafHighContextProgram.finished_scratch b regs high _ (by decide)).symm
  · rw [LeafHighContextProgram.finished_frame a regs high i hc,
      LeafHighContextProgram.finished_frame b regs high i hc]
    exact hf i hi

private theorem samples_offControl {a b : Factor.Data} (hf : OffControl a b)
    (h190 : b.stacks 190=[]) (h191 : b.stacks 191=[]) : OffControl (Samples.prepared a) b := by
  intro i hi
  by_cases h0 : i=190
  · subst i
    simp only [Samples.prepared_stacks,Function.update_of_ne (by decide : (190 : Fin 768)≠191),
      Function.update_same,h190]
  by_cases h1 : i=191
  · subst i
    simp only [Samples.prepared_stacks,Function.update_same,h191]
  exact (Samples.prepared_frame a i h0 h1).trans (hf i hi)

variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k initial hg W V L)

private theorem branch_190_empty (counter : List Bool) (regs : Fin 4 → Bool)
    (high : List Bool) : (PreparedNodeReady.branch p counter regs high).stacks 190=[] := by
  rw [PreparedNodeReady.branch,LeafHighContextProgram.finished_frame _ regs high 190 (by decide)]
  simp only [Function.update_of_ne (by decide : (190 : Fin 768)≠330)]
  rw [Marked.Wide.maskCopied_frame _ 190 (by decide)]
  exact Query.prepared_190 _

private theorem branch_191_empty (counter : List Bool) (regs : Fin 4 → Bool)
    (high : List Bool) : (PreparedNodeReady.branch p counter regs high).stacks 191=[] := by
  rw [PreparedNodeReady.branch,LeafHighContextProgram.finished_frame _ regs high 191 (by decide)]
  simp only [Function.update_of_ne (by decide : (191 : Fin 768)≠330)]
  rw [Marked.Wide.maskCopied_frame _ 191 (by decide)]
  exact Query.prepared_191 _

 theorem invariant_collector_frame (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (regs : Fin 4 → Bool) (high : List Bool) :
    ∀i,i∉PreparedNodeReady.branchControlPorts →
      (Samples.prepared (LeafHighContextProgram.finished (Residual.Native.outerReference a) regs high)).stacks i=
      (PreparedNodeReady.branch p (a.stacks 330) regs high).stacks i := by
  let base := Marked.Wide.maskCopied (Query.prepared p.out)
  have h0 : OffControl (Residual.Native.outerReference a)
      ⟨base.regs,Function.update base.stacks 330 (a.stacks 330)⟩ := by
    intro i hi
    exact (outer_offControl a i hi).trans
      ((invariant_offControl ha i hi).trans (counter_offControl base (a.stacks 330) i hi))
  apply samples_offControl (high_offControl h0 regs high)
  · exact branch_190_empty p (a.stacks 330) regs high
  · exact branch_191_empty p (a.stacks 330) regs high

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
