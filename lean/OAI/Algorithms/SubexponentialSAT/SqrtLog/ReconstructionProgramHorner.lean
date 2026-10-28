import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramCalls
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram

namespace OAI.Algorithms

/-! Physical staging of local CRT correction evaluation. The dense correction
is consumed from 244; its value at the retained point 263 is returned on 264. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

abbrev command (multiply add : Cmd 16 256) : Code :=
  move 244 246 ;; copy 263 247 ;; copy 243 248 ;; copy 104 250 ;; copy 104 240 ;;
  lowerCall (HornerProgram.command multiply add) 246 240 ;;
  move 240 264 ;; clearMany [247,250]

def budget (J W Km Ka : ℕ) : ℕ :=
  HornerProgram.budget J W Km Ka + 6 * J * W + 31 * W + 7 * J + 39

def cleanPorts : List (Fin 320) := [120,240,241,245,246,247,248,250,251,252,264,318,319]

theorem command_run {C : Type*} (encode : C → List Bool)
    (multiply add : Cmd 16 256) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (d : Data) (P : List C) (point zero : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp Km)
    (ha : ServiceSpec (d.stacks ∘ localPorts) encode add addOp Ka)
    (hw : ∀ a, (encode a).length = W)
    (hP : d.stacks 244 = HornerProgram.encodePolynomial encode P)
    (hx : d.stacks 263 = encode point) (hz : d.stacks 104 = encode zero)
    (hJ : (d.stacks 243).length = P.length)
    (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
    ∃ n ≤ budget P.length W Km Ka, ∃ rf,
      Eval (command multiply add) n d
        ⟨rf, Function.update (Function.update d.stacks 244 [])
          264 (encode (HornerProgram.fold (HornerProgram.stepValue mulOp addOp point) P.reverse zero))⟩ := by
  let value := HornerProgram.fold (HornerProgram.stepValue mulOp addOp point) P.reverse zero
  let d1 := moved d 244 246
  let d2 := afterCopy d1 263 247 0 1
  let d3 := afterCopy d2 243 248 0 1
  let d4 := afterCopy d3 104 250 0 1
  let d5 := afterCopy d4 104 240 0 1
  have h1 := move_run d 244 246 (by decide) (by decide) (by decide)
    (hc 319 (by simp [cleanPorts])) (hc 246 (by simp [cleanPorts]))
  have h2 := copy_run d1 263 247 (by decide) (by decide) (by decide)
    (by simpa [d1, moved] using hc 318 (by simp [cleanPorts]))
  have h3 := copy_run d2 243 248 (by decide) (by decide) (by decide)
    (by simpa [d2, d1, afterCopy, StackRoutines.copyStacks, moved] using hc 318 (by simp [cleanPorts]))
  have h4 := copy_run d3 104 250 (by decide) (by decide) (by decide)
    (by simpa [d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved] using hc 318 (by simp [cleanPorts]))
  have h5 := copy_run d4 104 240 (by decide) (by decide) (by decide)
    (by simpa [d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved] using hc 318 (by simp [cleanPorts]))
  let s := d5.stacks ∘ localPorts
  have hf : LowFrame (d.stacks ∘ localPorts) s := by
    intro i hi
    have hn (q : Fin 320) (hq : 205 ≤ q.val) : localPorts i ≠ q := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = q.val at hv
      omega
    simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      Function.comp_def, hn 240 (by decide), hn 244 (by decide), hn 246 (by decide),
      hn 247 (by decide), hn 248 (by decide), hn 250 (by decide)]
  have hscalar := HornerProgram.command_run s encode multiply add mulOp addOp Km Ka W
    (CRTLocalProgram.serviceSpec_frame hm hf) (CRTLocalProgram.serviceSpec_frame ha hf) hw P point zero
    (by simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      localPorts, hP])
    (by simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      localPorts, hx, hc 247 (by simp [cleanPorts])])
    (by simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      localPorts, hz, hc 240 (by simp [cleanPorts])])
    (by simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      localPorts, hJ, hc 248 (by simp [cleanPorts])])
    (by simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      localPorts, hz, hw, hc 250 (by simp [cleanPorts])])
    (by simpa [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved,
      localPorts] using hc 120 (by simp [cleanPorts]))
    (by simpa [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved,
      localPorts] using hc 241 (by simp [cleanPorts]))
    (by simp [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts])
    (by simpa [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved,
      localPorts] using hc 245 (by simp [cleanPorts]))
    (by simpa [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved,
      localPorts] using hc 251 (by simp [cleanPorts]))
    (by simpa [s, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved,
      localPorts] using hc 252 (by simp [cleanPorts]))
  obtain ⟨nl, hnl, rl, hl⟩ := lowerCall_run (HornerProgram.command multiply add) 246 240 d5 _
    (HornerProgram.budget P.length W Km Ka) hscalar
  have hs : Function.extend localPorts
      (Function.update (Function.update (Function.update s 246 []) 240 (encode value)) 248 []) d5.stacks =
      Function.update (Function.update (Function.update d5.stacks 246 []) 240 (encode value)) 248 [] := by
    rw [ProgramLinking.extend_update localPorts.injective,
      ProgramLinking.extend_update localPorts.injective, ProgramLinking.extend_update localPorts.injective]
    rw [lower_extend_project]
    rfl
  change Eval _ nl d5 ⟨rl, Function.extend localPorts
    (Function.update (Function.update (Function.update s 246 []) 240 (encode value)) 248 []) d5.stacks⟩ at hl
  rw [hs] at hl
  let d6 : Data := ⟨rl, Function.update (Function.update (Function.update d5.stacks 246 [])
    240 (encode value)) 248 []⟩
  have h6 := move_run d6 240 264 (by decide) (by decide) (by decide)
    (by simpa [d6, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved]
      using hc 319 (by simp [cleanPorts]))
    (by simpa [d6, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, moved]
      using hc 264 (by simp [cleanPorts]))
  let d7 := moved d6 240 264
  have h7 := clearMany_run d7 [247,250]
  have hfinal : (SubexpSetupStorage.clearManyState [247,250] d7).stacks =
      Function.update (Function.update d.stacks 244 []) 264 (encode value) := by
    funext i
    by_cases h240 : i = 240 <;> by_cases h246 : i = 246 <;> by_cases h248 : i = 248 <;>
      by_cases h247 : i = 247 <;> by_cases h250 : i = 250 <;>
      simp [SubexpSetupStorage.clearManyState, SubexpSetupStorage.clearState,
        d7, d6, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
        Function.update_apply, h240, h246, h248, h247, h250,
        hc 240 (by simp [cleanPorts]), hc 246 (by simp [cleanPorts]),
        hc 248 (by simp [cleanPorts]), hc 247 (by simp [cleanPorts]), hc 250 (by simp [cleanPorts])]
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (hl.seq (h6.seq h7))))))
  have hstate : SubexpSetupStorage.clearManyState [247,250] d7 =
      (⟨(SubexpSetupStorage.clearManyState [247,250] d7).regs,
        Function.update (Function.update d.stacks 244 []) 264 (encode value)⟩ : Data) :=
    state_ext rfl hfinal
  rw [hstate] at hrun
  refine ⟨_, ?_, _, hrun⟩
  have hpLen := HornerProgram.encodePolynomial_length encode W hw P
  simp [d7, d6, d5, d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
    SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearState,
    hP, hx, hz, hw, hpLen, hJ, budget,
    hc 247 (by simp [cleanPorts]), hc 250 (by simp [cleanPorts])]
  nlinarith

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

end OAI.Algorithms
