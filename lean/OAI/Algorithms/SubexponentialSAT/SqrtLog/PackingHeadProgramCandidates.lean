import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramEmit
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-! A fixed producer of all incremental head scores from the candidate alphabet
and actual flattened prior-head table. No selected pair records are inputs. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open Subexp

abbrev Data := State 8 12

def ports : RecordPrograms.Ports 8 12 where
  tag := 5
  present := 6
  found := 7
  source := 8
  payload := 0
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def baseState (rows : List (List Bool)) (acc : List Bool) : Data :=
  ⟨fun i => decide (i=6),![[],rows.flatten,[],[],[],List.replicate rows.length true,[],[],[],acc,[],[]]⟩
def boundary (rows : List (List Bool)) (acc tail candidate : List Bool) : Data :=
  RecordPrograms.state ports (baseState rows acc) false true false tail candidate

abbrev reverse : Cmd 8 12 := .call (reverseProgram 0 2 3 0 1)

theorem reverse_eval (rows : List (List Bool)) (acc tail candidate : List Bool) :
    Eval reverse (9*candidate.length+7) (boundary rows acc tail candidate.reverse)
      (boundary rows acc tail candidate) := by
  have h := SubexpScanPrimitives.reverse_eval (boundary rows acc tail candidate.reverse)
    0 2 3 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [boundary,RecordPrograms.state,ports,baseState])
    (by simp [boundary,RecordPrograms.state,ports,baseState])
  have hz : afterReverse (boundary rows acc tail candidate.reverse) 0 0 1 =
      boundary rows acc tail candidate := by
    apply state_ext <;> funext i <;> fin_cases i <;>
      simp [afterReverse,reverseStacks,boundary,RecordPrograms.state,ports,baseState,readRegs]
  rw [hz] at h
  simpa [reverse,boundary,RecordPrograms.state,ports] using h

def reg (i : Fin 5) : Fin 8 := i.castAdd 3
def low (i : Fin 8) : Fin 12 := i.castAdd 4
theorem reg_injective : Function.Injective reg := Fin.castAdd_injective _ _
theorem low_injective : Function.Injective low := Fin.castAdd_injective _ _

abbrev score : Cmd 8 12 := .call
  (ProgramLinking.liftProgram PackingHeadProgramPreserve.program reg low)

def scored (rows : List (List Bool)) (acc tail candidate : List Bool) : Data :=
  let d := boundary rows acc tail candidate
  ⟨d.regs,Function.update d.stacks 4
    (List.replicate (PackingHeadProgramPrefix.score candidate rows) false)⟩

theorem score_eval (rows : List (List Bool)) (acc tail candidate : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    ∃ n ≤ rows.length*(21*candidate.length+20)+14,
      Eval score n (boundary rows acc tail candidate) (scored rows acc tail candidate) := by
  let d := boundary rows acc tail candidate
  let a := PackingHeadProgramPreserve.state candidate rows.flatten rows.length []
  let b := PackingHeadProgramPreserve.state candidate rows.flatten rows.length
    (List.replicate (PackingHeadProgramPrefix.score candidate rows) false)
  have ha : embedState reg low d a=d := by
    apply embedState_eq_of_ports reg low d d a reg_injective low_injective
    · intro i; fin_cases i <;> simp [a,d,PackingHeadProgramPreserve.state,boundary,RecordPrograms.state,ports,baseState,reg]
    · intros; rfl
    · intro i; fin_cases i <;> simp [a,d,PackingHeadProgramPreserve.state,boundary,RecordPrograms.state,ports,baseState,low]
    · intros; rfl
  have hb : embedState reg low d b=scored rows acc tail candidate := by
    apply embedState_eq_of_ports reg low d _ b reg_injective low_injective
    · intro i; fin_cases i <;> simp [b,scored,PackingHeadProgramPreserve.state,boundary,RecordPrograms.state,ports,baseState,reg]
    · intros; rfl
    · intro i; fin_cases i <;> simp [b,scored,PackingHeadProgramPreserve.state,boundary,RecordPrograms.state,ports,baseState,low]
    · intro i hi
      have h4 : i ≠ 4 := fun h => hi ⟨4,by simpa [low] using h.symm⟩
      simp [scored,d,h4]
  obtain ⟨n,hn,ht⟩ := PackingHeadProgramPreserve.program_run candidate rows [] hlen
  simp only [List.append_nil] at ht
  have he := eval_call_lifted PackingHeadProgramPreserve.program reg low d
    reg_injective low_injective (a:=a) (b:=b) ht
  exact ⟨n,hn,by simpa only [ha,hb,score] using he⟩

abbrev reset : Cmd 8 12 := .seq RegisterResetProgram.all (.base (.atom (.set 6 true)))
def resetState (d : Data) : Data := ⟨fun i => decide (i=6),d.stacks⟩
theorem reset_eval (d : Data) : Eval reset 9 d (resetState d) := by
  have h := (RegisterResetProgram.all_eval d).seq
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (6 : Fin 8) true)
      (RegisterResetProgram.zeroed d)))
  convert h using 1
  apply state_ext
  · funext i; fin_cases i <;> simp [resetState,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]
  · rfl

abbrev clear : Cmd 8 12 := .call (clearProgram 0 0 1)
abbrev callback : Cmd 8 12 := .seq reverse (.seq score (.seq PackingProgram.Streams.emit (.seq clear reset)))

def callbackCost (rows : List (List Bool)) (candidate : List Bool) : ℕ :=
  rows.length*(21*candidate.length+20)+11*candidate.length+
    4*PackingHeadProgramPrefix.score candidate rows+41

theorem callback_eval (rows : List (List Bool)) (acc tail candidate : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    ∃ n ≤ callbackCost rows candidate,
      Eval callback n (boundary rows acc tail candidate.reverse)
        (boundary rows (CandidateScoreProgram.reverseRecord
          (List.replicate (PackingHeadProgramPrefix.score candidate rows) false) acc) tail []) := by
  have hr := reverse_eval rows acc tail candidate
  obtain ⟨n,hn,hs⟩ := score_eval rows acc tail candidate hlen
  obtain ⟨e,he,he4,he9,hef⟩ := PackingProgram.Streams.emit_eval (scored rows acc tail candidate)
  let f : Data := ⟨readRegs e.regs 0 1 none,Function.update e.stacks 0 []⟩
  have hc : Eval clear (2*(e.stacks 0).length+3) e f :=
    .call _ (SubexponentialSAT.ListRegisterProgram.clear_run 0 0 1 e.regs e.stacks)
  have hf := reset_eval f
  have h0 : e.stacks 0=candidate := by
    simpa [scored,boundary,RecordPrograms.state,ports] using hef 0 (by decide) (by decide)
  have hend : resetState f = boundary rows (CandidateScoreProgram.reverseRecord
      (List.replicate (PackingHeadProgramPrefix.score candidate rows) false) acc) tail [] := by
    apply state_ext
    · funext i; fin_cases i <;> simp [resetState,boundary,RecordPrograms.state,ports,baseState]
    · funext i
      fin_cases i
      · rfl
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (1 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (1 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (1 : Fin 12) ≠ 8)] using
          hef 1 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (2 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (2 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (2 : Fin 12) ≠ 8)] using
          hef 2 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (3 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (3 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (3 : Fin 12) ≠ 8)] using
          hef 3 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored] using he4
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (5 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (5 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (5 : Fin 12) ≠ 8)] using
          hef 5 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (6 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (6 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (6 : Fin 12) ≠ 8)] using
          hef 6 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (7 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (7 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (7 : Fin 12) ≠ 8)] using
          hef 7 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (8 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (8 : Fin 12) ≠ 0), Function.update_same] using
          hef 8 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored] using he9
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (10 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (10 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (10 : Fin 12) ≠ 8)] using
          hef 10 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (11 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (11 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (11 : Fin 12) ≠ 8)] using
          hef 11 (by decide) (by decide)
  rw [hend] at hf
  have hh := hr.seq (hs.seq (he.seq (hc.seq hf)))
  refine ⟨_,?_,hh⟩
  simp only [scored,boundary,RecordPrograms.state,ports,Function.update_same,List.length_replicate,h0]
  unfold callbackCost
  omega

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
