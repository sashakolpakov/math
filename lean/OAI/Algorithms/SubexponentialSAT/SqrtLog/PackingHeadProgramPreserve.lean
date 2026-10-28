import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIdentity

namespace OAI.Algorithms

/-! A source-preserving wrapper for the actual prefix scan. The only input
streams are one candidate, the flattened prior words, and their unary count. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open scoped BigOperators

abbrev Data := State 5 8

def state (candidate table : List Bool) (n : ℕ) (out : List Bool)
    (tableCopy countCopy : List Bool := []) : Data :=
  ⟨fun _ => false, ![candidate,table,[],[],out,List.replicate n true,tableCopy,countCopy]⟩

abbrev copyTable : Cmd 5 8 := .call (copyProgram 1 6 2 0 1)
abbrev copyCount : Cmd 5 8 := .call (copyProgram 5 7 2 0 1)

theorem copyTable_eval (candidate table : List Bool) (n : ℕ) (out : List Bool) :
    Eval copyTable (7*table.length+5) (state candidate table n out)
      (state candidate table n out table []) := by
  have h := copy_eval (state candidate table n out) 1 6 2 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state])
  have hz : afterCopy (state candidate table n out) 1 6 0 1 = state candidate table n out table [] := by
    apply state_ext <;> funext i <;> fin_cases i <;> simp [state,afterCopy,copyStacks,readRegs]
  rw [hz] at h
  simpa [copyTable,state] using h

theorem copyCount_eval (candidate table : List Bool) (n : ℕ) (out : List Bool) :
    Eval copyCount (7*n+5) (state candidate table n out table [])
      (state candidate table n out table (List.replicate n true)) := by
  have h := copy_eval (state candidate table n out table []) 5 7 2 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state])
  have hz : afterCopy (state candidate table n out table []) 5 7 0 1 =
      state candidate table n out table (List.replicate n true) := by
    apply state_ext <;> funext i <;> fin_cases i <;> simp [state,afterCopy,copyStacks,readRegs]
  rw [hz] at h
  simpa [copyCount,state] using h

def ports : Fin 6 → Fin 8 := ![0,6,2,3,4,7]
theorem ports_injective : Function.Injective ports := by decide

abbrev scan : Cmd 5 8 :=
  .call (ProgramLinking.liftProgram PackingHeadProgramPrefix.program id ports)

theorem scan_eval (candidate : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    Eval scan (1+PackingHeadProgramPrefix.loopCost candidate rows+1)
      (state candidate rows.flatten rows.length out rows.flatten (List.replicate rows.length true))
      (state candidate rows.flatten rows.length
        (List.replicate (PackingHeadProgramPrefix.score candidate rows) false++out)) := by
  let d := state candidate rows.flatten rows.length out rows.flatten (List.replicate rows.length true)
  let a := PackingHeadProgramPrefix.state false candidate rows.flatten [] rows.length out
  let b := PackingHeadProgramPrefix.state false candidate [] [] 0
    (List.replicate (PackingHeadProgramPrefix.score candidate rows) false++out)
  have ha : embedState id ports d a = d := by
    apply embedState_eq_of_ports id ports d d a Function.injective_id ports_injective
    · intro i; fin_cases i <;> simp [a,d,state,PackingHeadProgramPrefix.state]
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> simp [a,d,state,ports,PackingHeadProgramPrefix.state,PackingHeadProgramPrefix.unary]
    · intros; rfl
  have hb : embedState id ports d b = state candidate rows.flatten rows.length
      (List.replicate (PackingHeadProgramPrefix.score candidate rows) false++out) := by
    apply embedState_eq_of_ports id ports d _ b Function.injective_id ports_injective
    · intro i; fin_cases i <;> simp [b,state,PackingHeadProgramPrefix.state]
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> simp [b,state,ports,PackingHeadProgramPrefix.state,PackingHeadProgramPrefix.unary]
    · intro i hi
      have h4 : i ≠ 4 := fun h => hi ⟨4,by simpa [ports] using h.symm⟩
      have h6 : i ≠ 6 := fun h => hi ⟨1,by simpa [ports] using h.symm⟩
      have h7 : i ≠ 7 := fun h => hi ⟨5,by simpa [ports] using h.symm⟩
      fin_cases i <;> simp_all [d,state,ports]
  have ht := compiled_halt_trace (PackingHeadProgramPrefix.command_eval candidate rows out hlen) 0 4
  have he := eval_call_lifted PackingHeadProgramPrefix.program id ports d
    Function.injective_id ports_injective (a:=a) (b:=b) ht
  simpa only [ha,hb,scan] using he

abbrev command : Cmd 5 8 := .seq copyTable (.seq copyCount scan)
abbrev program : Program 5 8 (size command+1) := compiled command 0 4

theorem command_eval (candidate : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    Eval command (7*rows.flatten.length+7*rows.length+PackingHeadProgramPrefix.loopCost candidate rows+12)
      (state candidate rows.flatten rows.length out)
      (state candidate rows.flatten rows.length
        (List.replicate (PackingHeadProgramPrefix.score candidate rows) false++out)) := by
  have h := (copyTable_eval candidate rows.flatten rows.length out).seq
    ((copyCount_eval candidate rows.flatten rows.length out).seq (scan_eval candidate rows out hlen))
  convert h using 1 ; first | rfl | omega

theorem flatten_length (candidate : List Bool) (rows : List (List Bool))
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    rows.flatten.length=rows.length*candidate.length := by
  induction rows with
  | nil => simp
  | cons word rows ih =>
    simp only [List.flatten_cons,List.length_append,List.length_cons]
    rw [hlen word (by simp),ih (by intro row hr; exact hlen row (by simp [hr]))]
    ring

theorem program_run (candidate : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    RunsIn program (rows.length*(21*candidate.length+20)+14)
      ((state candidate rows.flatten rows.length out).withPC (some program.entry))
      ((state candidate rows.flatten rows.length
        (List.replicate (PackingHeadProgramPrefix.score candidate rows) false++out)).withPC none) := by
  refine ⟨_,?_,compiled_halt_trace (command_eval candidate rows out hlen) 0 4⟩
  have h := PackingHeadProgramPrefix.loopCost_le candidate rows hlen
  rw [flatten_length candidate rows hlen]
  nlinarith

theorem score_words {r Q : ℕ} (candidate : MulticolorTypes.Word r Q)
    (prior : List (MulticolorTypes.Word r Q)) :
    PackingHeadProgramPrefix.score (Subexp.ReadPlan.encodeWord candidate)
      (prior.map Subexp.ReadPlan.encodeWord) =
    (prior.map (fun word => ∑ t : Fin Q, if candidate t = word t then 1 else 0)).sum := by
  unfold PackingHeadProgramPrefix.score
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro word _
  exact Packing.encodeWord_and_count candidate word

end SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve

end OAI.Algorithms
