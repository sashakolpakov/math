import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Fixed parser-based views of an actual framed word alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentRecordViews

open BitProgram StructuredCalls TupleProgram

abbrev Data := State 3 3

abbrev data (v p f : Bool) (src acc out : List Bool) : Data :=
  ⟨![v, p, f], ![src, acc, out]⟩

def firstTwo : Fin 2 → Fin 3 := Fin.castAdd 1

theorem firstTwo_injective : Function.Injective firstTwo := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 3 => x.val) h)

abbrev parse : Cmd 3 3 :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram firstTwo firstTwo)

theorem parse_eval (v p f : Bool) (bits rest acc out : List Bool) :
    Eval parse (6 * bits.length + 4)
      (data v p f (Encoding.frame bits ++ rest) acc out)
      (data false true f rest (bits.reverse ++ acc) out) := by
  let a := data v p f (Encoding.frame bits ++ rest) acc out
  let b := data false true f rest (bits.reverse ++ acc) out
  have ha : embedState firstTwo firstTwo a
      (⟨ParserProgram.pair v p, ParserProgram.pair (Encoding.frame bits ++ rest) acc⟩ : State 2 2) = a := by
    apply embedState_eq_of_ports _ _ _ _ _ firstTwo_injective firstTwo_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState firstTwo firstTwo a
      (⟨ParserProgram.pair false true, ParserProgram.pair rest (bits.reverse ++ acc)⟩ : State 2 2) = b := by
    apply embedState_eq_of_ports _ _ _ _ _ firstTwo_injective firstTwo_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact (hi ⟨0, rfl⟩).elim | exact (hi ⟨1, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact (hi ⟨0, rfl⟩).elim | exact (hi ⟨1, rfl⟩).elim
  have h := eval_call_lifted ParserProgram.frameProgram firstTwo firstTwo a
    firstTwo_injective firstTwo_injective
    (a := (⟨ParserProgram.pair v p,
      ParserProgram.pair (Encoding.frame bits ++ rest) acc⟩ : State 2 2))
    (b := (⟨ParserProgram.pair false true,
      ParserProgram.pair rest (bits.reverse ++ acc)⟩ : State 2 2))
    (ParserProgram.frame_trace bits rest acc v p)
  simpa only [parse, ha, hb] using h

abbrev pop : Cmd 3 3 := .base (.atom (.pop 0 2 1))

theorem pop_eval (v p f b : Bool) (src acc out : List Bool) :
    Eval pop 1 (data v p f (b :: src) acc out) (data v true b src acc out) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 3) 2 1)
    (data v p f (b :: src) acc out))
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [
      StructuredProgram.Atom.instr, execInstr, readRegs]
  · funext i; fin_cases i <;> simp [
      StructuredProgram.Atom.instr, execInstr, readRegs]

abbrev afterTag (rows : List (List Bool)) (rest acc out : List Bool) : Data :=
  match rows with
  | [] => data false true false rest acc out
  | bits :: rows => data false true true
      (Encoding.frame bits ++ (ProgramEncoding.encodeRecords rows ++ rest)) acc out

theorem pop_records_eval (p f : Bool) (rows : List (List Bool)) (rest acc out : List Bool) :
    Eval pop 1 (data false p f (ProgramEncoding.encodeRecords rows ++ rest) acc out)
      (afterTag rows rest acc out) := by
  cases rows with
  | nil => simpa [afterTag, ProgramEncoding.encodeRecords, Encoding.encodeList] using
      pop_eval false p f false rest acc out
  | cons bits rows =>
      simpa [afterTag, ProgramEncoding.encodeRecords, Encoding.encodeList, List.append_assoc] using
        pop_eval false p f true
          (Encoding.frame bits ++ (ProgramEncoding.encodeRecords rows ++ rest)) acc out

abbrev loop : Cmd 3 3 := .while 2 (.seq parse pop)

theorem loop_eval (rows : List (List Bool)) (rest acc out : List Bool) :
    Eval loop (6 * (rows.map List.length).sum + 6 * rows.length + 1)
      (afterTag rows rest acc out)
      (data false true false rest (rows.flatten.reverse ++ acc) out) := by
  induction rows generalizing acc with
  | nil => simpa [afterTag] using
      (Eval.while_false (body := .seq parse pop) (test := (2 : Fin 3))
        (a := data false true false rest acc out) rfl)
  | cons bits rows ih =>
      have hp := parse_eval false true true bits (ProgramEncoding.encodeRecords rows ++ rest) acc out
      have ht := pop_records_eval true true rows rest (bits.reverse ++ acc) out
      have h := Eval.while_true (test := (2 : Fin 3))
        (a := afterTag (bits :: rows) rest acc out) rfl
        (hp.seq ht) (ih (bits.reverse ++ acc))
      convert h using 1 <;>
        simp [ List.reverse_append, List.append_assoc, Nat.mul_add] ; omega

abbrev transfer : Cmd 3 3 := .call (StackRoutines.transferProgram 1 2 0 1)

theorem transfer_eval (v p f : Bool) (src acc out : List Bool) :
    Eval transfer (3 * acc.length + 3) (data v p f src acc out)
      (data false false f src [] (acc.reverse ++ out)) := by
  have h := TupleProgram.transfer_eval (1 : Fin 3) 2 (0 : Fin 3) 1
    (by decide) (by decide) (data v p f src acc out)
  convert h using 1
  · simp []
  · apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [ readRegs]
    · funext i; fin_cases i <;> simp [ StackRoutines.transferStacks]

abbrev setFirst : Cmd 3 3 := .base (.atom (.set 0 false))

theorem setFirst_eval (v p f : Bool) (src acc out : List Bool) :
    Eval setFirst 1 (data v p f src acc out) (data false p f src acc out) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 3) false)
    (data v p f src acc out))
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> rfl
  · rfl

abbrev flatten : Cmd 3 3 := .seq setFirst (.seq pop (.seq loop transfer))
def flattenProgram := compiled flatten 0 2

theorem flatten_eval (v p f : Bool) (rows : List (List Bool)) (rest out : List Bool) :
    Eval flatten (9 * (rows.map List.length).sum + 6 * rows.length + 6)
      (data v p f (ProgramEncoding.encodeRecords rows ++ rest) [] out)
      (data false false false rest [] (rows.flatten ++ out)) := by
  have h1 := setFirst_eval v p f (ProgramEncoding.encodeRecords rows ++ rest) [] out
  have h2 := pop_records_eval p f rows rest [] out
  have h3 := loop_eval rows rest [] out
  simp only [List.append_nil] at h3
  have h4 := transfer_eval false true false rest rows.flatten.reverse out
  simp only [List.reverse_reverse] at h4
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1
  simp [List.length_flatten]
  omega

theorem flatten_trace (v p f : Bool) (rows : List (List Bool)) (rest out : List Bool) :
    Trace flattenProgram (9 * (rows.map List.length).sum + 6 * rows.length + 7)
      ((data v p f (ProgramEncoding.encodeRecords rows ++ rest) [] out).withPC
        (some flattenProgram.entry))
      ((data false false false rest [] (rows.flatten ++ out)).withPC none) := by
  convert compiled_halt_trace (flatten_eval v p f rows rest out) 0 2 using 1
  all_goals first | rfl

abbrev setFlag : Cmd 3 3 := .base (.atom (.set 2 false))

theorem setFlag_eval (v p f : Bool) (src acc out : List Bool) :
    Eval setFlag 1 (data v p f src acc out) (data v p false src acc out) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.set (2 : Fin 3) false)
    (data v p f src acc out))
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> rfl
  · rfl

/-- Read the actual first record. The remaining framed list is returned on 0. -/
abbrev first : Cmd 3 3 := .seq pop (.seq parse (.seq transfer setFlag))
def firstProgram := compiled first 0 2

theorem first_trace (v p f : Bool) (bits : List Bool) (rows : List (List Bool)) :
    Trace firstProgram (9 * bits.length + 10)
      ((data v p f (ProgramEncoding.encodeRecords (bits :: rows)) [] []).withPC
        (some firstProgram.entry))
      ((data false false false (ProgramEncoding.encodeRecords rows) [] bits).withPC none) := by
  have h1 := pop_eval v p f true
    (Encoding.frame bits ++ ProgramEncoding.encodeRecords rows) [] []
  have h2 := parse_eval v true true bits (ProgramEncoding.encodeRecords rows) [] []
  simp only [List.append_nil] at h2
  have h3 := transfer_eval false true true (ProgramEncoding.encodeRecords rows) bits.reverse []
  simp only [List.reverse_reverse, List.append_nil] at h3
  have h4 := setFlag_eval false false true (ProgramEncoding.encodeRecords rows) [] bits
  have h := h1.seq (h2.seq (h3.seq h4))
  have hr := compiled_halt_trace h 0 2
  convert hr using 1
  · rfl
  · simp only [List.length_reverse]
    omega
  · simp [firstProgram, ProgramEncoding.encodeRecords, Encoding.encodeList]

end SubexponentialSAT.Subexp.AssignmentRecordViews

end OAI.Algorithms
