import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeMassFootprint
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeReachable

namespace OAI.Algorithms

/-! The branch accumulator is erased only in the proof-side reference state.
Exact-time replay puts the caller's original accumulators back. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay LeafNodeSamplesProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

 def outerReference (a : Data) : Data := rebaseState outerTape (fun _ => []) a
 def outerRestore (a b : Data) : Data := rebaseState outerTape a.stacks b

 @[simp] theorem outerReference_regs (a : Data) : (outerReference a).regs=a.regs := rfl
 @[simp] theorem outerRestore_regs (a b : Data) : (outerRestore a b).regs=b.regs := rfl
 theorem outerReference_empty (a : Data) (i : Fin 768) (hi : outerTape i) :
    (outerReference a).stacks i=[] := by
  simp [outerReference,rebaseState,rebaseStacks,hi]
 theorem outerReference_visible (a : Data) (i : Fin 768) (hi : ¬outerTape i) :
    (outerReference a).stacks i=a.stacks i := by
  simp [outerReference,rebaseState,rebaseStacks,hi]
 theorem outerRestore_visible (a b : Data) (i : Fin 768) (hi : ¬outerTape i) :
    (outerRestore a b).stacks i=b.stacks i := by
  simp [outerRestore,rebaseState,rebaseStacks,hi]

 theorem outerReference_wordBound (a : Data) (W : ℕ)
    (hw : ∀ i : Fin 768,¬outerTape i → (a.stacks i).length ≤ W) :
    ∀ i,((outerReference a).stacks i).length ≤ W := by
  intro i
  by_cases hi : outerTape i
  · rw [outerReference_empty a i hi]; simp
  · rw [outerReference_visible a i hi]
    exact hw i hi

 theorem outerRestore_reference (a : Data) : outerRestore a (outerReference a)=a := by
  apply congrArg (StructuredProgram.State.mk a.regs)
  funext i
  by_cases hi : outerTape i <;> simp [outerReference,rebaseState,rebaseStacks,hi]

 theorem outer_replay_eval (hc : AvoidsCmd outerTape Residual.command)
    (a b : Data) (k : ℕ) (he : Eval Residual.command k (outerReference a) b) :
    Eval Residual.command k a (outerRestore a b) := by
  have hh := eval_rebase outerTape hc he a.stacks
  change Eval Residual.command k (outerRestore a (outerReference a)) (outerRestore a b) at hh
  rw [outerRestore_reference] at hh
  exact hh

 theorem outer_replay_frame (a b : Data)
    (hb : b.stacks=Function.update (outerReference a).stacks 323 (b.stacks 323)) :
    (outerRestore a b).stacks=Function.update a.stacks 323 ((outerRestore a b).stacks 323) := by
  rw [outerRestore_visible a b 323 (by decide)]
  change rebaseStacks outerTape a.stacks b.stacks=Function.update a.stacks 323 (b.stacks 323)
  rw [hb,rebaseStacks_update outerTape a.stacks (outerReference a).stacks 323 (b.stacks 323) (by decide)]
  exact congrArg (fun st : Fin 768 → List Bool => Function.update st 323 (b.stacks 323))
    (congrArg StructuredProgram.State.stacks (outerRestore_reference a))

 theorem outer_replay_result (hc : AvoidsCmd outerTape Residual.command)
    (a : Data) (K count width : ℕ)
    (h : ∃ time out,time ≤ K ∧ Eval Residual.command time (outerReference a) out ∧
      BinaryArithmetic.toNat (out.stacks 323)=count ∧ (out.stacks 323).length ≤ width ∧
      out.stacks 324=[] ∧ out.stacks=Function.update (outerReference a).stacks 323 (out.stacks 323) ∧
      RegFrame (outerReference a).regs out.regs) :
    ∃ time out,time ≤ K ∧ Eval Residual.command time a out ∧
      BinaryArithmetic.toNat (out.stacks 323)=count ∧ (out.stacks 323).length ≤ width ∧
      out.stacks 324=[] ∧ out.stacks=Function.update a.stacks 323 (out.stacks 323) ∧
      RegFrame a.regs out.regs := by
  obtain ⟨time,out,ht,he,hc',hw,h324,hf,hr⟩ := h
  refine ⟨time,outerRestore a out,ht,outer_replay_eval hc a out time he,?_,?_,?_,
    outer_replay_frame a out hf,hr⟩
  · simpa only [outerRestore_visible a out 323 (by decide)] using hc'
  · simpa only [outerRestore_visible a out 323 (by decide)] using hw
  · simpa only [outerRestore_visible a out 324 (by decide)] using h324

 @[simp] theorem outer_highBound (a : Data) (h : ℕ) :
    highBound (outerReference a) h=highBound a h := by
  simp only [highBound,outerReference_visible a 338 (by decide)]

 @[simp] theorem outer_sampleBudget (a : Data) (nodes : ℕ → List Bool)
    (cost : ℕ → ℕ) (maxJet Q : ℕ) :
    sampleBudget (outerReference a) nodes cost maxJet Q=sampleBudget a nodes cost maxJet Q := by
  simp only [sampleBudget,Samples.prepareCost,
    Samples.prepared_frame _ 256 (by decide) (by decide),
    outerReference_visible a 190 (by decide),outerReference_visible a 191 (by decide),
    outerReference_visible a 256 (by decide)]

end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
