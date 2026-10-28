import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramAnd
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! A fixed counted loop over the existing flattened head prefix. Every
iteration copies the candidate and counts its true bitwise intersections with
one prefix word. No per-coordinate metadata or selected-pair stream is supplied. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives

abbrev Data := State 5 6
abbrev unary (n : ℕ) := List.replicate n true

def state (active : Bool) (candidate table work : List Bool) (n : ℕ) (out : List Bool) : Data :=
  ⟨![active,active,false,false,false],![candidate,table,work,[],out,unary n]⟩

abbrev guard : Cmd 5 6 := .base (.atom (.pop 5 0 1))

def flag (n : ℕ) : Bool := decide (0 < n)

theorem guard_eval (candidate table : List Bool) (n : ℕ) (out : List Bool) :
    Eval guard 1 (state false candidate table [] n out)
      (state (flag n) candidate table [] (n-1) out) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (5 : Fin 6) (0 : Fin 5) 1)
    (state false candidate table [] n out)
  apply Eval.base
  convert h using 1
  cases n <;>
    apply state_ext <;> funext i <;> fin_cases i <;>
    simp [state,flag,unary,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr,readRegs,List.replicate_succ]

abbrev copy : Cmd 5 6 := .call (copyProgram 0 2 3 0 1)

theorem copy_eval (candidate table : List Bool) (n : ℕ) (out : List Bool) :
    Eval copy (7*candidate.length+5) (state true candidate table [] n out)
      (state false candidate table candidate n out) := by
  have h := SubexpScanPrimitives.copy_eval (state true candidate table [] n out)
    0 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by simp [state])
  have hz : afterCopy (state true candidate table [] n out) 0 2 0 1 =
      state false candidate table candidate n out := by
    apply state_ext <;> funext i <;> fin_cases i <;> simp [state,afterCopy,copyStacks,readRegs]
  rw [hz] at h
  simpa [copy,state] using h

def zipPorts : Fin 3 → Fin 6 := ![2,1,4]
theorem zipPorts_injective : Function.Injective zipPorts := by decide

abbrev zip : Cmd 5 6 := .call (ProgramLinking.liftProgram PackingHeadProgramAnd.program id zipPorts)

theorem zip_eval (candidate word tail : List Bool) (n : ℕ) (out : List Bool)
    (hlen : candidate.length=word.length) :
    Eval zip (PackingHeadProgramAnd.steps candidate word)
      (state false candidate (word++tail) candidate n out)
      (state false candidate tail [] n
        (List.replicate (PackingHeadProgramAnd.jointTrue candidate word) false++out)) := by
  let d := state false candidate (word++tail) candidate n out
  let a : State 5 3 := ⟨fun _ => false,PackingHeadProgramAnd.stackData candidate (word++tail) out⟩
  let b : State 5 3 := ⟨fun _ => false,PackingHeadProgramAnd.stackData [] tail
    (List.replicate (PackingHeadProgramAnd.jointTrue candidate word) false++out)⟩
  have ha : embedState id zipPorts d a=d := by
    apply embedState_eq_of_ports id zipPorts d d a Function.injective_id zipPorts_injective
    · intro i; fin_cases i <;> simp [a,d,state]
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> simp [a,d,state,zipPorts,PackingHeadProgramAnd.stackData]
    · intros; rfl
  have hb : embedState id zipPorts d b = state false candidate tail [] n
      (List.replicate (PackingHeadProgramAnd.jointTrue candidate word) false++out) := by
    apply embedState_eq_of_ports id zipPorts d _ _ Function.injective_id zipPorts_injective
    · intro i; fin_cases i <;> simp [b,state]
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> simp [b,state,zipPorts,PackingHeadProgramAnd.stackData]
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨1,by simpa [zipPorts] using h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨0,by simpa [zipPorts] using h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨2,by simpa [zipPorts] using h.symm⟩
      fin_cases i <;> simp_all [d,state]
  have ht := PackingHeadProgramAnd.trace (fun _ => false) candidate word tail out hlen
  have he := eval_call_lifted PackingHeadProgramAnd.program id zipPorts d
    Function.injective_id zipPorts_injective (a:=a) (b:=b) ht
  simpa only [ha,hb,zip] using he

abbrev body : Cmd 5 6 := .seq copy (.seq zip guard)
abbrev loop : Cmd 5 6 := .while 1 body
abbrev command : Cmd 5 6 := .seq guard loop

def score (candidate : List Bool) (rows : List (List Bool)) : ℕ :=
  (rows.map (PackingHeadProgramAnd.jointTrue candidate)).sum

def loopCost (candidate : List Bool) : List (List Bool) → ℕ
  | [] => 1
  | word::rows => (7*candidate.length+7+PackingHeadProgramAnd.steps candidate word)+loopCost candidate rows

def entry (candidate : List Bool) (rows : List (List Bool)) (out : List Bool) : Data :=
  state (flag rows.length) candidate rows.flatten [] (rows.length-1) out

theorem body_eval (candidate word : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : candidate.length=word.length) :
    Eval body (7*candidate.length+6+PackingHeadProgramAnd.steps candidate word)
      (entry candidate (word::rows) out)
      (entry candidate rows (List.replicate (PackingHeadProgramAnd.jointTrue candidate word) false++out)) := by
  have hc := copy_eval candidate (word++rows.flatten) rows.length out
  have hz := zip_eval candidate word rows.flatten rows.length out hlen
  have hg := guard_eval candidate rows.flatten rows.length
    (List.replicate (PackingHeadProgramAnd.jointTrue candidate word) false++out)
  have h := hc.seq (hz.seq hg)
  convert h using 1 <;> first | rfl | omega

theorem loop_eval (candidate : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    Eval loop (loopCost candidate rows) (entry candidate rows out)
      (state false candidate [] [] 0 (List.replicate (score candidate rows) false++out)) := by
  induction rows generalizing out with
  | nil => simpa [loop,loopCost,entry,flag,score] using
      (Eval.while_false (test:=1) (body:=body) (a:=entry candidate [] out) (by simp [entry,state,flag]))
  | cons word rows ih =>
    have hb := body_eval candidate word rows out (hlen word (by simp)).symm
    have hi := ih (List.replicate (PackingHeadProgramAnd.jointTrue candidate word) false++out)
      (by intro row hr; exact hlen row (by simp [hr]))
    have h := Eval.while_true (test:=1) (body:=body) (by simp [entry,state,flag]) hb hi
    convert h using 1
    · simp only [loopCost]; omega
    · congr 1
      rw [show score candidate (word::rows) = score candidate rows +
        PackingHeadProgramAnd.jointTrue candidate word by simp [score,Nat.add_comm],
        List.replicate_add,List.append_assoc]

/-- Existing candidate bytes and flattened prefix bytes are the real inputs.
The unary prefix length is consumed; the candidate is preserved. -/
theorem command_eval (candidate : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    Eval command (1+loopCost candidate rows)
      (state false candidate rows.flatten [] rows.length out)
      (state false candidate [] [] 0 (List.replicate (score candidate rows) false++out)) :=
  (guard_eval candidate rows.flatten rows.length out).seq (loop_eval candidate rows out hlen)

theorem loopCost_le (candidate : List Bool) (rows : List (List Bool))
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    loopCost candidate rows ≤ rows.length*(14*candidate.length+13)+1 := by
  induction rows with
  | nil => simp [loopCost]
  | cons word rows ih =>
    have hs := PackingHeadProgramAnd.steps_le candidate word (hlen word (by simp)).symm
    have ht := ih (by intro row hr; exact hlen row (by simp [hr]))
    simp only [loopCost,List.length_cons]
    nlinarith

abbrev program : Program 5 6 (size command+1) := compiled command 0 4

theorem program_run (candidate : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    RunsIn program (rows.length*(14*candidate.length+13)+3)
      ((state false candidate rows.flatten [] rows.length out).withPC (some program.entry))
      ((state false candidate [] [] 0 (List.replicate (score candidate rows) false++out)).withPC none) := by
  have he := command_eval candidate rows out hlen
  exact ⟨1+loopCost candidate rows+1,by have := loopCost_le candidate rows hlen; omega,
    compiled_halt_trace he 0 4⟩

theorem primitive_run (candidate : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(rows.length*(14*candidate.length+13)+3))
      (primitiveCfg program ((state false candidate rows.flatten [] rows.length out).withPC (some program.entry)))
      (primitiveCfg program ((state false candidate [] [] 0
        (List.replicate (score candidate rows) false++out)).withPC none)) :=
  BitProgram.primitive_execution program (program_run candidate rows out hlen)

end SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix

end OAI.Algorithms
