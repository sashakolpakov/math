import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgramNative

namespace OAI.Algorithms

/-! Preserving shell for the assignment merge. Only output9 and registers
change; the masters and both reserved words are preserved. -/
namespace SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

abbrev Data := LeafWeightProgram.Native.Data
abbrev tapes := LeafWeightProgram.Native.tapes
abbrev data := LeafWeightProgram.Native.data
abbrev copy := LeafWeightProgram.Native.copy

private theorem copy_eval (src dst : Fin 10) (hsd : src ≠ dst)
    (hst : src ≠ 8) (htd : (8 : Fin 10) ≠ dst)
    (r : Fin 8 → Bool) (stk : Fin 10 → List Bool) (ht : stk 8 = []) :
    Eval (copy src dst) (7*(stk src).length+5) ⟨r,stk⟩
      ⟨readRegs r 0 3 none,copyStacks src dst stk⟩ := by
  apply Eval.call
  have he := halt_after_trace _
    (copyProgram_trace src dst 8 (0 : Fin 8) 3 hsd hst htd (by decide) r stk ht) 7 rfl rfl
  simpa [StructuredProgram.State.withPC,copyResult,copyProgram,Nat.add_assoc] using he

def stackMap : Fin 5 → Fin 10 := ![5,6,7,9,8]
theorem stackMap_injective : Function.Injective stackMap := by decide

private theorem embedKernel (r old : Fin 8 → Bool)
    (a h b u v x y z oldX oldY oldZ out oldOut : List Bool) :
    embedState id stackMap (data old a h b u v oldX oldY oldZ oldOut)
      (LeafAssignmentMergeProgram.data r x y z out []) = data r a h b u v x y z out := by
  apply embedState_eq_of_ports id stackMap _ _ _ Function.injective_id stackMap_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h5 : i ≠ 5 := by
      intro e
      apply hi
      exact ⟨0, by simpa [stackMap] using e.symm⟩
    have h6 : i ≠ 6 := by
      intro e
      apply hi
      exact ⟨1, by simpa [stackMap] using e.symm⟩
    have h7 : i ≠ 7 := by
      intro e
      apply hi
      exact ⟨2, by simpa [stackMap] using e.symm⟩
    have h9 : i ≠ 9 := by
      intro e
      apply hi
      exact ⟨3, by simpa [stackMap] using e.symm⟩
    have hs : tapes a h b u v x y z out =
        Function.update (Function.update (Function.update (Function.update
          (tapes a h b u v oldX oldY oldZ oldOut) 5 x) 6 y) 7 z) 9 out := by
      rw [LeafWeightProgram.Native.update5,LeafWeightProgram.Native.update6,
        LeafWeightProgram.Native.update7,LeafWeightProgram.Native.update9]
    change tapes a h b u v x y z out i =
      tapes a h b u v oldX oldY oldZ oldOut i
    rw [hs]
    rw [Function.update_of_ne h9,Function.update_of_ne h7,
      Function.update_of_ne h6,Function.update_of_ne h5]

abbrev scan : Cmd 8 10 :=
  .call (ProgramLinking.liftProgram LeafAssignmentMergeProgram.program id stackMap)

theorem scan_eval (r : Fin 8 → Bool) (a h b u v : List Bool)
    (hah : a.length=h.length) (hab : a.length=b.length) :
    ∃ rf, Eval scan (9*a.length+6) (data r a h b u v a h b [])
      (data rf a h b u v [] [] [] (merge a h b)) := by
  obtain ⟨rf,he⟩ := LeafAssignmentMergeProgram.program_trace r a h b hah hab
  have hx := eval_call_lifted LeafAssignmentMergeProgram.program id stackMap
    (data r a h b u v a h b []) Function.injective_id stackMap_injective he
  rw [embedKernel,embedKernel] at hx
  exact ⟨rf,hx⟩

abbrev command : Cmd 8 10 := .seq (copy 0 5)
  (.seq (copy 1 6) (.seq (copy 2 7) scan))

/-- Local3 and4 are arbitrary preserved words, so this helper can share the
weight helper's ABI without overwriting the cached ring constants. -/
theorem command_eval (r : Fin 8 → Bool) (a h b u v : List Bool)
    (hah : a.length=h.length) (hab : a.length=b.length) :
    ∃ rf, Eval command (30*a.length+21) (data r a h b u v [] [] [] [])
      (data rf a h b u v [] [] [] (merge a h b)) := by
  have e1 := copy_eval 0 5 (by decide) (by decide) (by decide) r
    (tapes a h b u v [] [] [] []) rfl
  change Eval (copy 0 5) (7*a.length+5)
    (data r a h b u v [] [] [] [])
    ⟨readRegs r 0 3 none,Function.update (tapes a h b u v [] [] [] []) 5 (a++[])⟩ at e1
  rw [List.append_nil,LeafWeightProgram.Native.update5] at e1
  let r1 := readRegs r 0 3 none
  have e2 := copy_eval 1 6 (by decide) (by decide) (by decide) r1
    (tapes a h b u v a [] [] []) rfl
  change Eval (copy 1 6) (7*h.length+5)
    (data r1 a h b u v a [] [] [])
    ⟨readRegs r1 0 3 none,Function.update (tapes a h b u v a [] [] []) 6 (h++[])⟩ at e2
  rw [List.append_nil,LeafWeightProgram.Native.update6] at e2
  let r2 := readRegs r1 0 3 none
  have e3 := copy_eval 2 7 (by decide) (by decide) (by decide) r2
    (tapes a h b u v a h [] []) rfl
  change Eval (copy 2 7) (7*b.length+5)
    (data r2 a h b u v a h [] [])
    ⟨readRegs r2 0 3 none,Function.update (tapes a h b u v a h [] []) 7 (b++[])⟩ at e3
  rw [List.append_nil,LeafWeightProgram.Native.update7] at e3
  obtain ⟨rf,ef⟩ := scan_eval (readRegs r2 0 3 none) a h b u v hah hab
  refine ⟨rf, ?_⟩
  have he := e1.seq (e2.seq (e3.seq ef))
  convert he using 1 ; omega

def program := compiled command 0 9

theorem program_trace (r : Fin 8 → Bool) (a h b u v : List Bool)
    (hah : a.length=h.length) (hab : a.length=b.length) :
    ∃ rf, Trace program (30*a.length+22)
      ((data r a h b u v [] [] [] []).withPC (some program.entry))
      ((data rf a h b u v [] [] [] (merge a h b)).withPC none) := by
  obtain ⟨rf,he⟩ := command_eval r a h b u v hah hab
  exact ⟨rf, by simpa [program, Nat.add_assoc] using compiled_halt_trace he 0 9⟩

theorem program_control_size : size command + 1 = 38 := rfl

theorem program_lifted {R S : ℕ} (ρ : Fin 8 → Fin R) (σ : Fin 10 → Fin S)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (frame : StructuredProgram.State R S) (r : Fin 8 → Bool)
    (a h b u v : List Bool) (hah : a.length=h.length) (hab : a.length=b.length) :
    ∃ rf, Eval (.call (ProgramLinking.liftProgram program ρ σ)) (30*a.length+22)
      (embedState ρ σ frame (data r a h b u v [] [] [] []))
      (embedState ρ σ frame (data rf a h b u v [] [] [] (merge a h b))) := by
  obtain ⟨rf,he⟩ := program_trace r a h b u v hah hab
  exact ⟨rf,eval_call_lifted program ρ σ frame hρ hσ he⟩

/-- The actual program outputs the full original-ID assignment needed for
incidence beta, choosing the head assignment exactly at the supplied mask. -/
theorem program_ofFn {n : ℕ} (r : Fin 8 → Bool) (a h b : Fin n → Bool)
    (u v : List Bool) :
    ∃ rf, Trace program (30*n+22)
      ((data r (List.ofFn a) (List.ofFn h) (List.ofFn b) u v [] [] [] []).withPC
        (some program.entry))
      ((data rf (List.ofFn a) (List.ofFn h) (List.ofFn b) u v [] [] []
        (List.ofFn fun i => if h i then a i else b i)).withPC none) := by
  obtain ⟨rf,he⟩ := program_trace r (List.ofFn a) (List.ofFn h) (List.ofFn b) u v
    (by simp) (by simp)
  exact ⟨rf, by simpa [merge_ofFn] using he⟩

end SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native

end OAI.Algorithms
