import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! # A fixed re-framer for the scalar alphabet

Input records contain raw scalar words. Output records contain complete
scalar frames, so the tuple generator emits a concatenation of scalar
frames. The original alphabet is preserved; output order is reversed.
-/

namespace SubexponentialSAT.Subexp.ScalarAlphabetFrames

open BitProgram StructuredCalls TupleProgram

def outerPorts : RecordPrograms.Ports 6 7 :=
  ⟨0,1,2,1,2,by decide,by decide,by decide,by decide⟩

def firstPorts : RecordPrograms.Ports 6 7 :=
  ⟨3,4,5,2,3,by decide,by decide,by decide,by decide⟩

def secondPorts : RecordPrograms.Ports 6 7 :=
  ⟨3,4,5,4,5,by decide,by decide,by decide,by decide⟩

abbrev callback : Cmd 6 7 :=
  .seq (pushConst 3 3 false) (.seq (escape firstPorts)
    (.seq (.call (StackRoutines.transferProgram 3 4 3 4))
      (.seq (pushConst 5 3 false) (.seq (escape secondPorts) (pushConst 5 3 true)))))

def invariant (source : List Bool) (a : State 6 7) : Prop :=
  a.stacks 0 = source ∧ a.stacks 3 = [] ∧ a.stacks 4 = [] ∧ a.stacks 6 = []

theorem callback_contract (source : List Bool) :
    RecordPrograms.CallbackContractWith outerPorts callback (fun _ => false)
      (fun bits => 21 * bits.length + 23) (invariant source)
      (fun bits a b => b.stacks 5 = prependRecord (Encoding.frame bits) (a.stacks 5)) := by
  intro bits tail base hi
  let a := RecordPrograms.state outerPorts base false true false tail bits.reverse
  let b := pushedState 3 3 false a
  let c := escapedState firstPorts b
  let d : State 6 7 := ⟨readRegs c.regs 3 4 none,StackRoutines.transferStacks 3 4 c.stacks⟩
  let e := pushedState 5 3 false d
  let f := escapedState secondPorts e
  let g := pushedState 5 3 true f
  have h1 := pushConst_eval 3 3 false a
  have h2 := escape_eval_state firstPorts b
  have h3 := transfer_eval 3 4 3 4 (by decide) (by decide) c
  have h4 := pushConst_eval 5 3 false d
  have h5 := escape_eval_state secondPorts e
  have h6 := pushConst_eval 5 3 true f
  have hc3 : c.stacks 3 = Encoding.frame bits := by
    simp [c, b, a, firstPorts, RecordPrograms.state, outerPorts,
      hi.2.1,frame_eq_escaped]
  have hd4 : d.stacks 4 = (Encoding.frame bits).reverse := by
    simp [d, StackRoutines.transferStacks, c, b, a, firstPorts,
      RecordPrograms.state, outerPorts, hi.2.1, hi.2.2.1, frame_eq_escaped]
  have hg : RecordPrograms.state outerPorts g false true false tail [] = g := by
    apply RecordPrograms.state_eq_self <;>
      simp [g, f, e, d, c, b, a, readRegs, firstPorts, secondPorts,
        RecordPrograms.state, outerPorts, StackRoutines.transferStacks]
  refine ⟨21 * bits.length + 23,g,le_rfl,?_,?_,?_⟩
  · rcases hi with ⟨hi0,hi3,hi4,hi6⟩
    simp [invariant, g, f, e, d, c, b, a, firstPorts, secondPorts,
      RecordPrograms.state, outerPorts, StackRoutines.transferStacks, hi0, hi6]
  · simp [g, f, e, secondPorts, prependRecord,
      d, c, b, a, StackRoutines.transferStacks, firstPorts, RecordPrograms.state, outerPorts,
      frame_eq_escaped, List.append_assoc, hi.2.1, hi.2.2.1]
  · rw [hg]
    have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
    convert h using 1
    all_goals
      simp [a, b, e, firstPorts, secondPorts, RecordPrograms.state,
        outerPorts, hc3, hd4, Encoding.length_frame]
      omega

abbrev command : Cmd 6 7 :=
  .seq (pushConst 5 3 false)
    (.seq (.call (StackRoutines.copyProgram 0 1 6 3 4))
      (RecordPrograms.iterate outerPorts callback))

def program := compiled command 0 5

def inputState (records : Records) (regs : Fin 6 → Bool) : State 6 7 :=
  ⟨regs,fun i => if i = 0 then ProgramEncoding.encodeRecords records else []⟩

def outputState (records : Records) (regs : Fin 6 → Bool) : State 6 7 :=
  ⟨regs,fun i => if i = 0 then ProgramEncoding.encodeRecords records
    else if i = 5 then ProgramEncoding.encodeRecords ((records.map Encoding.frame).reverse) else []⟩

def budget (records : Records) : ℕ :=
  7 * (ProgramEncoding.encodeRecords records).length +
    RecordPrograms.budget (fun bits => 21 * bits.length + 23) records + 11

theorem program_run (records : Records) (regs : Fin 6 → Bool) :
    ∃ regs', RunsIn program (budget records)
      ((inputState records regs).withPC (some program.entry))
      ((outputState records regs').withPC none) := by
  let a := inputState records regs
  let b := pushedState 5 3 false a
  let c : State 6 7 := ⟨readRegs b.regs 3 4 none,StackRoutines.copyStacks 0 1 b.stacks⟩
  have h1 := pushConst_eval 5 3 false a
  have h2 := copy_eval 0 1 6 3 4 (by decide) (by decide) (by decide) (by decide) b
    (by simp [b, a, inputState])
  have hc : invariant (ProgramEncoding.encodeRecords records) c := by
    simp [invariant, c, b, a, StackRoutines.copyStacks, inputState]
  have hc5 : c.stacks 5 = ProgramEncoding.encodeRecords [] := by
    simp [c, b, a, StackRoutines.copyStacks, inputState,
      ProgramEncoding.encodeRecords, Encoding.encodeList]
  obtain ⟨n,next,hn,hnext,history,he⟩ := RecordPrograms.iterate_run_with
    outerPorts callback (fun _ => false) (fun bits => 21 * bits.length + 23)
    (invariant (ProgramEncoding.encodeRecords records))
    (fun bits a b => b.stacks 5 = prependRecord (Encoding.frame bits) (a.stacks 5))
    (callback_contract _) records [] c hc (c.regs 0) (c.regs 1) (c.regs 2)
  have hstart : RecordPrograms.state outerPorts c (c.regs 0) (c.regs 1) (c.regs 2)
      (Encoding.encodeList id records ++ []) [] = c := by
    apply RecordPrograms.state_eq_self <;>
      simp [c, b, a, outerPorts, StackRoutines.copyStacks, inputState,
        ProgramEncoding.encodeRecords]
  have hout := history.fold_of_false (by simp) (fun a => a.stacks 5)
    (fun out bits => prependRecord (Encoding.frame bits) out) (fun _ _ _ h => h)
  change next.stacks 5 = records.foldl
    (fun out bits => prependRecord (Encoding.frame bits) out) (c.stacks 5) at hout
  have hfold : records.foldl (fun out bits => prependRecord (Encoding.frame bits) out)
      (ProgramEncoding.encodeRecords []) =
      ProgramEncoding.encodeRecords ((records.map Encoding.frame).reverse) := by
    rw [← List.foldl_map (f := Encoding.frame) (g := fun out bits => prependRecord bits out)]
    rw [fold_prependRecord,appendEncoded_encodeRecords]
    simp
  rw [hc5,hfold] at hout
  let d := RecordPrograms.state outerPorts next false true false [] []
  have hd : d = outputState records d.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    rcases hnext with ⟨h0,h3,h4,h6⟩
    fin_cases i <;> simp [outerPorts, h0, h3, h4, h6, hout]
  have hany : records.any (fun _ => false) = false := by
    simp
  have he' : Eval (RecordPrograms.iterate outerPorts callback) n c d := by
    simpa only [hstart,hany,unread_false,d] using he
  rw [hd] at he'
  refine ⟨d.regs,_,?_,compiled_halt_trace (h1.seq (h2.seq he')) 0 5⟩
  simp only [b, a, inputState, Function.update_of_ne (by decide : (0 : Fin 7) ≠ 5)]
  dsimp [budget]
  omega

end SubexponentialSAT.Subexp.ScalarAlphabetFrames

end OAI.Algorithms
