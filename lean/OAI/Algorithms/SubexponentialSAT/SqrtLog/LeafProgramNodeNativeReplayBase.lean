import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay

namespace OAI.Algorithms

/-! One bounded reference execution suffices for every carried-buffer frame. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
open SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

def collectorTape (i : Fin 768) : Prop := i∈carriedPorts
instance : DecidablePred collectorTape := fun i=>inferInstanceAs (Decidable (i∈carriedPorts))

def masked (a : Data) : Data := rebaseState collectorTape (fun _=>[]) a

theorem masked_regs (a : Data) : (masked a).regs=a.regs := rfl

theorem masked_wordBound (a : Data) (B : ℕ) (h : LocalWordBound B a) : WordBound B (masked a) := by
  intro i
  by_cases hi : collectorTape i
  · simp [masked,rebaseState,rebaseStacks,hi]
  · simpa [masked,rebaseState,rebaseStacks,hi] using h i hi

theorem masked_visible (a : Data) (i : Fin 768) (hi : ¬collectorTape i) :
    (masked a).stacks i=a.stacks i := by simp [masked,rebaseState,rebaseStacks,hi]

theorem restore_masked (a : Data) : rebaseState collectorTape a.stacks (masked a)=a := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : collectorTape i <;> simp [masked,rebaseState,rebaseStacks,hi]

theorem restore_result (a : Data) (rr : Fin 40 → Bool) (bits : List Bool) :
    rebaseState collectorTape a.stacks
      (⟨rr,Function.update (Function.update (masked a).stacks 78 []) 102 bits⟩ : Data)=
      ⟨rr,Function.update (Function.update a.stacks 78 []) 102 bits⟩ := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · change rebaseStacks collectorTape a.stacks
      (Function.update (Function.update (masked a).stacks 78 []) 102 bits)=_
    rw [rebaseStacks_update _ _ _ _ _ (by decide),rebaseStacks_update _ _ _ _ _ (by decide)]
    have he : rebaseStacks collectorTape a.stacks (masked a).stacks=a.stacks :=
      congrArg (fun st : Data=>st.stacks) (restore_masked a)
    simpa only [rebaseState] using congrArg (fun f : Fin 768 → List Bool=>Function.update (Function.update f 78 []) 102 bits) he

/-- The public specialization below supplies the concrete structural footprint.
No initial bound is imposed on any carried buffer. -/
theorem replay_with_footprint (hcode : AvoidsCmd collectorTape Node.command)
    (a : Data) (rr : Fin 40 → Bool) (bits : List Bool) (k : ℕ)
    (h : Eval Node.command k (masked a)
      ⟨rr,Function.update (Function.update (masked a).stacks 78 []) 102 bits⟩) :
    Eval Node.command k a ⟨rr,Function.update (Function.update a.stacks 78 []) 102 bits⟩ := by
  have he := eval_rebase collectorTape hcode h a.stacks
  simpa only [restore_masked,restore_result] using he

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end OAI.Algorithms
