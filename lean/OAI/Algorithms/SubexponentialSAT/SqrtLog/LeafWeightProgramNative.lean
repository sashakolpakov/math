import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Preserving physical wrapper for the Boolean head-weight scan. The actual
ring zero and one are arbitrary runtime words, so the ring degree is dynamic. -/
namespace SubexponentialSAT.SqrtLog.LeafWeightProgram.Native

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

abbrev Data := StructuredProgram.State 8 10

abbrev tapes (a s h zero one x y z out : List Bool) : Fin 10 → List Bool :=
  ![a,s,h,zero,one,x,y,z,[],out]
abbrev data (r : Fin 8 → Bool) (a s h zero one x y z out : List Bool) : Data :=
  ⟨r,tapes a s h zero one x y z out⟩

@[simp] theorem update5 (a s h zero one x y z out v : List Bool) :
    Function.update (tapes a s h zero one x y z out) 5 v =
      tapes a s h zero one v y z out := by
  funext i; fin_cases i <;> simp [tapes]
@[simp] theorem update6 (a s h zero one x y z out v : List Bool) :
    Function.update (tapes a s h zero one x y z out) 6 v =
      tapes a s h zero one x v z out := by
  funext i; fin_cases i <;> simp [tapes]
@[simp] theorem update7 (a s h zero one x y z out v : List Bool) :
    Function.update (tapes a s h zero one x y z out) 7 v =
      tapes a s h zero one x y v out := by
  funext i; fin_cases i <;> simp [tapes]
@[simp] theorem update9 (a s h zero one x y z out v : List Bool) :
    Function.update (tapes a s h zero one x y z out) 9 v =
      tapes a s h zero one x y z v := by
  funext i; fin_cases i <;> simp [tapes]

abbrev copy (src dst : Fin 10) : Cmd 8 10 := .call (copyProgram src dst 8 0 3)

private theorem copy_eval (src dst : Fin 10) (hsd : src ≠ dst)
    (hst : src ≠ 8) (htd : (8 : Fin 10) ≠ dst)
    (r : Fin 8 → Bool) (stk : Fin 10 → List Bool) (ht : stk 8 = []) :
    Eval (copy src dst) (7*(stk src).length+5) ⟨r,stk⟩
      ⟨readRegs r 0 3 none,copyStacks src dst stk⟩ := by
  apply Eval.call
  have he := halt_after_trace _
    (copyProgram_trace src dst 8 (0 : Fin 8) 3 hsd hst htd (by decide) r stk ht) 7 rfl rfl
  simpa [StructuredProgram.State.withPC,copyResult,copyProgram,Nat.add_assoc] using he

abbrev stackMap : Fin 3 → Fin 10 := ![5,6,7]

theorem stackMap_injective : Function.Injective stackMap := by decide

private theorem embedKernel (r old : Fin 8 → Bool)
    (a s h zero one x y z oldX oldY oldZ out : List Bool) :
    embedState id stackMap (data old a s h zero one oldX oldY oldZ out)
      (LeafWeightProgram.data r x y z) = data r a s h zero one x y z out := by
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
    have hs : tapes a s h zero one x y z out =
        Function.update (Function.update (Function.update
          (tapes a s h zero one oldX oldY oldZ out) 5 x) 6 y) 7 z := by
      rw [update5,update6,update7]
    change tapes a s h zero one x y z out i =
      tapes a s h zero one oldX oldY oldZ out i
    rw [hs]
    rw [Function.update_of_ne h7,Function.update_of_ne h6,Function.update_of_ne h5]

abbrev scan : Cmd 8 10 :=
  .call (ProgramLinking.liftProgram LeafWeightProgram.program id stackMap)

theorem scan_eval (r : Fin 8 → Bool) (a s h zero one out : List Bool)
    (has : a.length = s.length) (hah : a.length = h.length) :
    ∃ rf, Eval scan (8*a.length+4) (data r a s h zero one a s h out)
      (data rf a s h zero one [] [] [] out) ∧ rf 6 = good a s h := by
  obtain ⟨rf,he,hv⟩ := LeafWeightProgram.program_trace r a s h has hah
  have hx := eval_call_lifted LeafWeightProgram.program id stackMap
    (data r a s h zero one a s h out) Function.injective_id stackMap_injective he
  rw [embedKernel,embedKernel] at hx
  exact ⟨rf,hx,hv⟩

abbrev select : Cmd 8 10 := .ite 6 (copy 4 9) (copy 3 9)
abbrev command : Cmd 8 10 := .seq (copy 0 5)
  (.seq (copy 1 6) (.seq (copy 2 7) (.seq scan select)))

def result (a s h zero one : List Bool) : List Bool :=
  if good a s h then one else zero

private theorem select_eval (r : Fin 8 → Bool) (a s h zero one : List Bool)
    (hr : r 6 = good a s h) :
    ∃ rf, Eval select (7*(result a s h zero one).length+6)
      (data r a s h zero one [] [] [] [])
      (data rf a s h zero one [] [] [] (result a s h zero one)) := by
  cases hg : good a s h with
  | false =>
    have he := copy_eval 3 9 (by decide) (by decide) (by decide) r
      (tapes a s h zero one [] [] [] []) rfl
    simp only [copyStacks] at he
    change Eval (copy 3 9) (7*zero.length+5)
      (data r a s h zero one [] [] [] [])
      ⟨readRegs r 0 3 none,Function.update (tapes a s h zero one [] [] [] []) 9 (zero++[])⟩ at he
    rw [List.append_nil,update9] at he
    refine ⟨readRegs r 0 3 none, ?_⟩
    simpa [select,result,hg,Nat.add_assoc] using
      (Eval.ite_false (by simpa [hg] using hr) he : Eval select _ _ _)
  | true =>
    have he := copy_eval 4 9 (by decide) (by decide) (by decide) r
      (tapes a s h zero one [] [] [] []) rfl
    simp only [copyStacks] at he
    change Eval (copy 4 9) (7*one.length+5)
      (data r a s h zero one [] [] [] [])
      ⟨readRegs r 0 3 none,Function.update (tapes a s h zero one [] [] [] []) 9 (one++[])⟩ at he
    rw [List.append_nil,update9] at he
    refine ⟨readRegs r 0 3 none, ?_⟩
    simpa [select,result,hg,Nat.add_assoc] using
      (Eval.ite_true (by simpa [hg] using hr) he : Eval select _ _ _)

/-- Every input word is preserved and all four private work stacks are empty
at return. Only the output word and registers can change. -/
theorem command_eval (r : Fin 8 → Bool) (a s h zero one : List Bool)
    (has : a.length = s.length) (hah : a.length = h.length) :
    ∃ rf, Eval command (29*a.length+7*(result a s h zero one).length+25)
      (data r a s h zero one [] [] [] [])
      (data rf a s h zero one [] [] [] (result a s h zero one)) := by
  have e1 := copy_eval 0 5 (by decide) (by decide) (by decide) r
    (tapes a s h zero one [] [] [] []) rfl
  change Eval (copy 0 5) (7*a.length+5)
    (data r a s h zero one [] [] [] [])
    ⟨readRegs r 0 3 none,Function.update (tapes a s h zero one [] [] [] []) 5 (a++[])⟩ at e1
  rw [List.append_nil,update5] at e1
  let r1 := readRegs r 0 3 none
  have e2 := copy_eval 1 6 (by decide) (by decide) (by decide) r1
    (tapes a s h zero one a [] [] []) rfl
  change Eval (copy 1 6) (7*s.length+5)
    (data r1 a s h zero one a [] [] [])
    ⟨readRegs r1 0 3 none,Function.update (tapes a s h zero one a [] [] []) 6 (s++[])⟩ at e2
  rw [List.append_nil,update6] at e2
  let r2 := readRegs r1 0 3 none
  have e3 := copy_eval 2 7 (by decide) (by decide) (by decide) r2
    (tapes a s h zero one a s [] []) rfl
  change Eval (copy 2 7) (7*h.length+5)
    (data r2 a s h zero one a s [] [])
    ⟨readRegs r2 0 3 none,Function.update (tapes a s h zero one a s [] []) 7 (h++[])⟩ at e3
  rw [List.append_nil,update7] at e3
  obtain ⟨rs,es,hs⟩ := scan_eval (readRegs r2 0 3 none) a s h zero one [] has hah
  obtain ⟨rf,ef⟩ := select_eval rs a s h zero one hs
  refine ⟨rf, ?_⟩
  have he := e1.seq (e2.seq (e3.seq (es.seq ef)))
  convert he using 1 ; omega

abbrev program := compiled command 0 9

theorem program_trace (r : Fin 8 → Bool) (a s h zero one : List Bool)
    (has : a.length = s.length) (hah : a.length = h.length) :
    ∃ rf, Trace program (29*a.length+7*(result a s h zero one).length+26)
      ((data r a s h zero one [] [] [] []).withPC (some program.entry))
      ((data rf a s h zero one [] [] [] (result a s h zero one)).withPC none) := by
  obtain ⟨rf,he⟩ := command_eval r a s h zero one has hah
  exact ⟨rf, by simpa [Nat.add_assoc] using compiled_halt_trace he 0 9⟩

theorem program_control_size : size command + 1 = 53 := rfl

theorem result_length (a s h zero one : List Bool) (W : ℕ)
    (hz : zero.length = W) (ho : one.length = W) :
    (result a s h zero one).length = W := by
  unfold result
  split <;> assumption

/-- Generic caller relocation preserves every nonlocal register and stack. -/
theorem program_lifted {R S : ℕ} (ρ : Fin 8 → Fin R) (σ : Fin 10 → Fin S)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (frame : StructuredProgram.State R S) (r : Fin 8 → Bool)
    (a s h zero one : List Bool) (has : a.length = s.length) (hah : a.length = h.length) :
    ∃ rf, Eval (.call (ProgramLinking.liftProgram program ρ σ))
      (29*a.length+7*(result a s h zero one).length+26)
      (embedState ρ σ frame (data r a s h zero one [] [] [] []))
      (embedState ρ σ frame (data rf a s h zero one [] [] [] (result a s h zero one))) := by
  obtain ⟨rf,he⟩ := program_trace r a s h zero one has hah
  exact ⟨rf,eval_call_lifted program ρ σ frame hρ hσ he⟩

end SubexponentialSAT.SqrtLog.LeafWeightProgram.Native

end OAI.Algorithms
