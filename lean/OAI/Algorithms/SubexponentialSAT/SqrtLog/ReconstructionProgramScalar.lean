import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramCalls

namespace OAI.Algorithms

/-! Framed outer calls to the native scalar ring arithmetic. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def safe (p : Fin 320) : Prop := p ≠ 240 ∧ p ≠ 241 ∧ p ≠ 244 ∧ p ≠ 318 ∧ p ≠ 319

abbrev binary (code : Cmd 16 256) (src right dst : Fin 320) : Code :=
  copy src 240 ;; copy right 241 ;; lowerCall code 240 244 ;; clear dst ;;
  move 244 dst ;; clearMany [240,241]

def cleanPorts : List (Fin 320) := [120,240,241,244,245,318,319]

theorem binary_run {C : Type*} (encode : C → List Bool) (code : Cmd 16 256)
    (op : C → C → C) (K W : ℕ) (d : Data) (src right dst : Fin 320)
    (hs : safe src) (hr : safe right) (hd : safe dst)
    (hcode : ServiceSpec (d.stacks ∘ localPorts) encode code op K)
    (hw : ∀ a, (encode a).length = W) (a b : C)
    (ha : d.stacks src = encode a) (hb : d.stacks right = encode b)
    (hdw : (d.stacks dst).length ≤ W)
    (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
    ∃ n ≤ K + 26 * W + 26, ∃ rf,
      Eval (binary code src right dst) n d ⟨rf, Function.update d.stacks dst (encode (op a b))⟩ := by
  rcases hs with ⟨hs0, hs1, hs4, hs8, hs9⟩
  rcases hr with ⟨hr0, hr1, hr4, hr8, hr9⟩
  rcases hd with ⟨hd0, hd1, hd4, hd8, hd9⟩
  let d1 := afterCopy d src 240 0 1
  let d2 := afterCopy d1 right 241 0 1
  let s := d2.stacks ∘ localPorts
  have h1 := copy_run d src 240 hs0 hs8 (by decide) (hc 318 (by simp [cleanPorts]))
  have h2 := copy_run d1 right 241 hr1 hr8 (by decide)
    (by simpa [d1, afterCopy, StackRoutines.copyStacks] using hc 318 (by simp [cleanPorts]))
  have hf : LowFrame (d.stacks ∘ localPorts) s := by
    intro i hi
    have h0 : localPorts i ≠ (240 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 240 at hv; omega
    have h1 : localPorts i ≠ (241 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 241 at hv; omega
    simp [s, d2, d1, afterCopy, StackRoutines.copyStacks, Function.comp_def, h0, h1]
  have hcall := CRTLocalProgram.serviceSpec_frame hcode hf s a b (CRTLocalProgram.lowFrame_refl s)
    (by simp [s, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts, ha,
      hc 240 (by simp [cleanPorts])])
    (by simp [s, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts, hb, hr0,
      hc 241 (by simp [cleanPorts])])
    (by simpa [s, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts]
      using hc 244 (by simp [cleanPorts]))
    (by simpa [s, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts]
      using hc 245 (by simp [cleanPorts]))
  obtain ⟨nl, hnl, rl, hl⟩ := lowerCall_run code 240 244 d2 _ K hcall
  have he : Function.extend localPorts (Function.update s 244 (encode (op a b))) d2.stacks =
      Function.update d2.stacks 244 (encode (op a b)) := by
    rw [ProgramLinking.extend_update localPorts.injective, lower_extend_project]
    rfl
  rw [he] at hl
  let d3 : Data := ⟨rl, Function.update d2.stacks 244 (encode (op a b))⟩
  have h3 := clear_run d3 dst
  let d4 := SubexpSetupStorage.clearState dst d3
  have h4 := move_run d4 244 dst (by decide) hd9 (Ne.symm hd4)
    (by simpa [d4, SubexpSetupStorage.clearState, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      Ne.symm hd9] using hc 319 (by simp [cleanPorts]))
    (by simp [d4, SubexpSetupStorage.clearState])
  let d5 := moved d4 244 dst
  have h5 := clearMany_run d5 [240,241]
  have hfinal : (SubexpSetupStorage.clearManyState [240,241] d5).stacks =
      Function.update d.stacks dst (encode (op a b)) := by
    funext i
    by_cases h0 : i = 240 <;> by_cases h1 : i = 241 <;> by_cases h4 : i = 244 <;>
      by_cases hd : i = dst <;>
      simp [SubexpSetupStorage.clearManyState, SubexpSetupStorage.clearState,
        d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
        Function.update_apply, h0, h1, h4, hd, hd0, hd1,
        Ne.symm hd0, Ne.symm hd1, Ne.symm hd4,
        hc 240 (by simp [cleanPorts]), hc 241 (by simp [cleanPorts]), hc 244 (by simp [cleanPorts])]
  have hrun := h1.seq (h2.seq (hl.seq (h3.seq (h4.seq h5))))
  have heq : SubexpSetupStorage.clearManyState [240,241] d5 =
      (⟨(SubexpSetupStorage.clearManyState [240,241] d5).regs,
        Function.update d.stacks dst (encode (op a b))⟩ : Data) := state_ext rfl hfinal
  rw [heq] at hrun
  refine ⟨_, ?_, _, hrun⟩
  simp [d5, d4, SubexpSetupStorage.clearState, d3, d2, d1, afterCopy, StackRoutines.copyStacks, SubexpSetupStorage.clearManyCost, ha, hb, hw, hr0, hd0, hd1, hd4,
    Ne.symm hd0, Ne.symm hd1, Ne.symm hd4,
    hc 240 (by simp [cleanPorts]), hc 241 (by simp [cleanPorts])]
  omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

end OAI.Algorithms
