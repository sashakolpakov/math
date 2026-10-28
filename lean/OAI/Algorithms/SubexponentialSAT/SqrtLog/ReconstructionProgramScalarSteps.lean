import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramScalar

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec)

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

abbrev negative (multiply : Cmd 16 256) : Code := binary multiply 259 211 263

abbrev accumulate (multiply add : Cmd 16 256) : Code :=
  binary multiply 262 264 263 ;; binary add 261 263 261 ;; clearMany [262,263,264]

theorem lower_update_high (s : Fin 320 → List Bool) (j : Fin 320) (h : 256 ≤ j.val)
    (word : List Bool) : (Function.update s j word) ∘ localPorts = s ∘ localPorts := by
  funext i
  have hne : localPorts i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = j.val at hv
    omega
  simp [ hne]

theorem negative_run {C : Type*} (encode : C → List Bool) (multiply : Cmd 16 256)
    (mulOp : C → C → C) (K W : ℕ) (d : Data) (node minusOne : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp K)
    (hw : ∀ a, (encode a).length = W)
    (hn : d.stacks 259 = encode node) (hminus : d.stacks 211 = encode minusOne)
    (h263 : d.stacks 263 = []) (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
    ∃ n ≤ K + 26 * W + 26, ∃ rf, Eval (negative multiply) n d
      ⟨rf, Function.update d.stacks 263 (encode (mulOp node minusOne))⟩ := by
  exact binary_run encode multiply mulOp K W d 259 211 263
    (by unfold safe; decide) (by unfold safe; decide) (by unfold safe; decide) hm hw node minusOne hn hminus
    (by simp [h263]) hc

theorem accumulate_run {C : Type*} (encode : C → List Bool) (multiply add : Cmd 16 256)
    (mulOp addOp : C → C → C) (Km Ka W : ℕ) (d : Data) (acc factor value point : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp Km)
    (ha : ServiceSpec (d.stacks ∘ localPorts) encode add addOp Ka)
    (hw : ∀ a, (encode a).length = W)
    (hacc : d.stacks 261 = encode acc) (hfactor : d.stacks 262 = encode factor)
    (hvalue : d.stacks 264 = encode value) (hpoint : d.stacks 263 = encode point)
    (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
    ∃ n ≤ Km + Ka + 58 * W + 61, ∃ rf, Eval (accumulate multiply add) n d
      ⟨rf, Function.update (Function.update (Function.update (Function.update d.stacks
        261 (encode (addOp acc (mulOp factor value)))) 262 []) 263 []) 264 []⟩ := by
  obtain ⟨n1, hn1, r1, h1⟩ := binary_run encode multiply mulOp Km W d 262 264 263
    (by unfold safe; decide) (by unfold safe; decide) (by unfold safe; decide) hm hw factor value hfactor hvalue
    (by simp [hpoint, hw]) hc
  let d1 : Data := ⟨r1, Function.update d.stacks 263 (encode (mulOp factor value))⟩
  have ha1 : ServiceSpec (d1.stacks ∘ localPorts) encode add addOp Ka := by
    simpa only [d1, lower_update_high d.stacks 263 (by decide)] using ha
  have hc1 : ∀ i ∈ cleanPorts, d1.stacks i = [] := by
    intro i hi
    have hne : i ≠ (263 : Fin 320) := by
      simp only [cleanPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [d1, hne] using hc i hi
  obtain ⟨n2, hn2, r2, h2⟩ := binary_run encode add addOp Ka W d1 261 263 261
    (by unfold safe; decide) (by unfold safe; decide) (by unfold safe; decide) ha1 hw acc (mulOp factor value)
    (by simpa [d1] using hacc) (by simp [d1]) (by simp [d1, hacc, hw]) hc1
  let d2 : Data := ⟨r2, Function.update d1.stacks 261 (encode (addOp acc (mulOp factor value)))⟩
  have h3 := clearMany_run d2 [262,263,264]
  have he : (SubexpSetupStorage.clearManyState [262,263,264] d2).stacks =
      Function.update (Function.update (Function.update (Function.update d.stacks
        261 (encode (addOp acc (mulOp factor value)))) 262 []) 263 []) 264 [] := by
    funext i
    by_cases h261 : i = 261 <;> by_cases h262 : i = 262 <;>
      by_cases h263 : i = 263 <;> by_cases h264 : i = 264 <;>
      simp [SubexpSetupStorage.clearManyState, SubexpSetupStorage.clearState,
        d2, d1, h261, h262, h263, h264]
  have heq : SubexpSetupStorage.clearManyState [262,263,264] d2 =
      (⟨(SubexpSetupStorage.clearManyState [262,263,264] d2).regs,
        Function.update (Function.update (Function.update (Function.update d.stacks
          261 (encode (addOp acc (mulOp factor value)))) 262 []) 263 []) 264 []⟩ : Data) := state_ext rfl he
  have hrun := h1.seq (h2.seq h3)
  rw [heq] at hrun
  refine ⟨_, ?_, _, hrun⟩
  simp [SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearState, d2, d1,
    hfactor, hvalue, hw]
  omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

end OAI.Algorithms
