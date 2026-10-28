import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives Subexp

def scoreBits (rows : List (List Bool)) (candidate : List Bool) : List Bool :=
  List.replicate (PackingHeadProgramPrefix.score candidate rows) false

def invariant (rows : List (List Bool)) (d : Data) : Prop := ∃ acc, d=baseState rows acc

def effect (rows : List (List Bool)) (bits : List Bool) (a b : Data) : Prop :=
  b.stacks 9 = CandidateScoreProgram.reverseRecord (scoreBits rows bits) (a.stacks 9)

def validPayload (rows : List (List Bool)) (bits : List Bool) : Prop :=
  ∀ row ∈ rows,row.length=bits.length

theorem callback_contract (rows : List (List Bool)) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost rows) (invariant rows) (effect rows) (validPayload rows) := by
  rintro bits tail base hv ⟨acc,rfl⟩
  obtain ⟨n,hn,he⟩ := callback_eval rows acc tail bits hv
  refine ⟨n,baseState rows (CandidateScoreProgram.reverseRecord (scoreBits rows bits) acc),hn,
    ⟨_,rfl⟩,?_,he⟩
  rfl

private theorem unread_false (records : List (List Bool)) :
    RecordPrograms.unread (fun _ => false) records [] = [] := by
  induction records with
  | nil => rfl
  | cons b bs ih => simpa only [RecordPrograms.unread,Bool.false_eq_true,ite_false] using ih

private theorem any_false (records : List (List Bool)) : records.any (fun _ => false) = false := by
  induction records <;> simp_all

def scoreRecords (rows candidates : List (List Bool)) : List (List Bool) :=
  candidates.map (scoreBits rows)

abbrev loop : Cmd 8 12 := RecordPrograms.iterate ports callback

def inputState (rows candidates : List (List Bool)) : Data :=
  RecordPrograms.state ports (baseState rows []) false false false
    (ProgramEncoding.encodeRecords candidates) []

theorem loop_eval (rows candidates : List (List Bool))
    (hlen : ∀ candidate ∈ candidates,validPayload rows candidate) :
    ∃ n ≤ 3+RecordPrograms.budget (callbackCost rows) candidates,
      Eval loop n (inputState rows candidates)
        (baseState rows (TupleProgram.appendEncoded (scoreRecords rows candidates) []).reverse) := by
  obtain ⟨n,next,hn,hnext,history,he⟩ := RecordPrograms.iterate_run_with_on ports callback
    (fun _ => false) (callbackCost rows) (invariant rows) (effect rows)
    (validPayload rows) (callback_contract rows) candidates [] (baseState rows [])
    hlen ⟨[],rfl⟩ false false false
  obtain ⟨acc,rfl⟩ := hnext
  have hout : acc=(TupleProgram.appendEncoded (scoreRecords rows candidates) []).reverse := by
    have h := history.fold_of_false (by simp) (fun d => d.stacks 9)
      (fun acc bits => CandidateScoreProgram.reverseRecord (scoreBits rows bits) acc)
      (fun _ _ _ h => h)
    have hm : candidates.foldl (fun acc bits =>
        CandidateScoreProgram.reverseRecord (scoreBits rows bits) acc) [] =
        (scoreRecords rows candidates).foldl (fun acc bits =>
          CandidateScoreProgram.reverseRecord bits acc) [] := by
      simp [scoreRecords,List.foldl_map]
    simpa [baseState,hm,CandidateScoreProgram.reverseRecord_fold] using h
  subst acc
  have hf : RecordPrograms.state ports (baseState rows
      (TupleProgram.appendEncoded (scoreRecords rows candidates) []).reverse)
      false true false [] [] = baseState rows
      (TupleProgram.appendEncoded (scoreRecords rows candidates) []).reverse := by
    apply RecordPrograms.state_eq_self <;> simp [ports,baseState]
  refine ⟨n,hn,?_⟩
  simpa only [any_false,unread_false,hf,ProgramEncoding.encodeRecords,inputState,List.append_nil,loop] using he

abbrev finish : Cmd 8 12 := .seq (TupleProgram.pushConst 9 0 false)
  (.call (reverseProgram 9 2 3 0 1))

theorem finish_bytes (records : List (List Bool)) :
    TupleProgram.appendEncoded records [] ++ [false] = ProgramEncoding.encodeRecords records := by
  simpa only [List.reverse_cons,List.reverse_reverse] using CandidateScoreProgram.reverseRecord_finish records

theorem finish_eval (rows candidates : List (List Bool)) :
    Eval finish (9*((TupleProgram.appendEncoded (scoreRecords rows candidates) []).length+1)+9)
      (baseState rows (TupleProgram.appendEncoded (scoreRecords rows candidates) []).reverse)
      (baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates))) := by
  let a := baseState rows (TupleProgram.appendEncoded (scoreRecords rows candidates) []).reverse
  let b := TupleProgram.pushedState 9 0 false a
  have hp := TupleProgram.pushConst_eval 9 0 false a
  have hr := SubexpScanPrimitives.reverse_eval b 9 2 3 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [b,a,baseState])
    (by simp [b,a,baseState])
  have hz : afterReverse b 9 0 1 =
      baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates)) := by
    apply state_ext
    · funext i; fin_cases i <;> simp [afterReverse,b,a,baseState,readRegs]
    · funext i; fin_cases i <;>
        simp [afterReverse,reverseStacks,b,a,baseState,
          finish_bytes]
  rw [hz] at hr
  convert hp.seq hr using 1 ;
    simp [b,a,baseState] ; omega

abbrev command : Cmd 8 12 := .seq loop finish
abbrev program : Program 8 12 (size command+1) := compiled command 8 9

def budget (rows candidates : List (List Bool)) : ℕ :=
  3+RecordPrograms.budget (callbackCost rows) candidates+
    (9*((TupleProgram.appendEncoded (scoreRecords rows candidates) []).length+1)+9)+1

theorem program_run (rows candidates : List (List Bool))
    (hlen : ∀ candidate ∈ candidates,validPayload rows candidate) :
    RunsIn program (budget rows candidates)
      ((inputState rows candidates).withPC (some program.entry))
      ((baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates))).withPC none) := by
  obtain ⟨n,hn,hl⟩ := loop_eval rows candidates hlen
  refine ⟨_,?_,compiled_halt_trace (hl.seq (finish_eval rows candidates)) 8 9⟩
  unfold budget
  omega

theorem primitive_run (rows candidates : List (List Bool))
    (hlen : ∀ candidate ∈ candidates,validPayload rows candidate) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program*budget rows candidates)
      (primitiveCfg program ((inputState rows candidates).withPC (some program.entry)))
      (primitiveCfg program
        ((baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates))).withPC none)) :=
  BitProgram.primitive_execution program (program_run rows candidates hlen)

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
