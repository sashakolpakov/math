import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! A counted parser for consecutive scalar frames.  The count is runtime
data; the output is the forward concatenation of the decoded scalar words. -/

namespace SubexponentialSAT.Subexp.ScalarBankProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 3 4

def data (v pr flag : Bool) (source accum output count : List Bool) : Data :=
  ⟨![v, pr, flag], ![source, accum, output, count]⟩

def parserRegs : Fin 2 → Fin 3 := Fin.castAdd 1
def parserStacks : Fin 2 → Fin 4 := Fin.castAdd 2

theorem parserRegs_injective : Function.Injective parserRegs := Fin.castAdd_injective _ _
theorem parserStacks_injective : Function.Injective parserStacks := Fin.castAdd_injective _ _

abbrev parse : Cmd 3 4 := .call
  (ProgramLinking.liftProgram ParserProgram.frameProgram parserRegs parserStacks)

theorem parse_eval (v pr flag : Bool) (bits rest accum output count : List Bool) :
    Eval parse (6 * bits.length + 4)
      (data v pr flag (Encoding.frame bits ++ rest) accum output count)
      (data false true flag rest (bits.reverse ++ accum) output count) := by
  let a := data v pr flag (Encoding.frame bits ++ rest) accum output count
  let b := data false true flag rest (bits.reverse ++ accum) output count
  have ha : embedState parserRegs parserStacks a
      (⟨ParserProgram.pair v pr,
        ParserProgram.pair (Encoding.frame bits ++ rest) accum⟩ : State 2 2) = a := by
    apply embedState_eq _ _ parserRegs_injective parserStacks_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have hb : embedState parserRegs parserStacks a
      (⟨ParserProgram.pair false true,
        ParserProgram.pair rest (bits.reverse ++ accum)⟩ : State 2 2) = b := by
    apply embedState_eq _ _ parserRegs_injective parserStacks_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact (hi ⟨0, rfl⟩).elim | exact (hi ⟨1, rfl⟩).elim
    · intro i hi
      fin_cases i <;> first | rfl | exact (hi ⟨0, rfl⟩).elim | exact (hi ⟨1, rfl⟩).elim
  have he := eval_call_lifted ParserProgram.frameProgram parserRegs parserStacks a
    parserRegs_injective parserStacks_injective
    (a := ⟨ParserProgram.pair v pr, ParserProgram.pair (Encoding.frame bits ++ rest) accum⟩)
    (b := ⟨ParserProgram.pair false true, ParserProgram.pair rest (bits.reverse ++ accum)⟩)
    (ParserProgram.frame_trace bits rest accum v pr)
  simpa only [parse, ha, hb] using he

abbrev pop : Cmd 3 4 := .base (.atom (.pop 3 0 2))

theorem pop_eval (v pr flag : Bool) (source accum output count : List Bool) :
    Eval pop 1 (data v pr flag source accum output count)
      (data (count.head?.getD false) pr count.head?.isSome source accum output count.tail) := by
  have he := Eval.base (StructuredProgram.Eval.atom (.pop (3 : Fin 4) 0 2)
    (data v pr flag source accum output count))
  convert he using 1
  apply state_ext
  · funext i; fin_cases i <;>
      simp [data, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, readRegs]
  · funext i; fin_cases i <;>
      simp [data, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]

def ready (rows : List (List Bool)) (rest accum output : List Bool) : Data :=
  data ((List.replicate rows.length true).head?.getD false) true
    (List.replicate rows.length true).head?.isSome
    (MatrixProgramSupport.words rows ++ rest) accum output
    (List.replicate rows.length true).tail

abbrev loop : Cmd 3 4 := .while 2 (.seq parse pop)

theorem loop_eval (rows : List (List Bool)) (rest accum output : List Bool) :
    Eval loop (6 * (rows.map List.length).sum + 6 * rows.length + 1)
      (ready rows rest accum output)
      (data false true false rest (rows.flatten.reverse ++ accum) output []) := by
  induction rows generalizing accum with
  | nil =>
    simpa [ready, data, MatrixProgramSupport.words] using
      (Eval.while_false (body := .seq parse pop) (test := (2 : Fin 3))
        (a := ready [] rest accum output) rfl)
  | cons bits rows ih =>
    have hp := parse_eval true true true bits
      (MatrixProgramSupport.words rows ++ rest) accum output (List.replicate rows.length true)
    have ht := pop_eval false true true
      (MatrixProgramSupport.words rows ++ rest) (bits.reverse ++ accum) output
      (List.replicate rows.length true)
    have hstep : Eval (.seq parse pop) (6 * bits.length + 4 + 1)
        (ready (bits :: rows) rest accum output)
        (ready rows rest (bits.reverse ++ accum) output) := by
      simpa [ready, List.replicate_succ, MatrixProgramSupport.words, List.append_assoc]
        using hp.seq ht
    have he := Eval.while_true (test := (2 : Fin 3))
      (a := ready (bits :: rows) rest accum output) (by simp [ready, data])
      hstep (ih (bits.reverse ++ accum))
    convert he using 1 <;>
      simp [List.reverse_append, List.append_assoc, Nat.mul_add]; omega

abbrev setPresent : Cmd 3 4 := .base (.atom (.set 1 true))

theorem setPresent_eval (v pr flag : Bool) (source accum output count : List Bool) :
    Eval setPresent 1 (data v pr flag source accum output count)
      (data v true flag source accum output count) := by
  have he := Eval.base (StructuredProgram.Eval.atom (.set (1 : Fin 3) true)
    (data v pr flag source accum output count))
  convert he using 1
  apply state_ext
  · funext i; fin_cases i <;> rfl
  · rfl

abbrev transfer : Cmd 3 4 := .call (StackRoutines.transferProgram 1 2 0 1)

theorem transfer_eval (v pr flag : Bool) (source accum output count : List Bool) :
    Eval transfer (3 * accum.length + 3) (data v pr flag source accum output count)
      (data false false flag source [] (accum.reverse ++ output) count) := by
  have he := TupleProgram.transfer_eval (1 : Fin 4) 2 (0 : Fin 3) 1
    (by decide) (by decide) (data v pr flag source accum output count)
  convert he using 1
  · rfl
  · apply state_ext
    · funext i; fin_cases i <;> simp [data, readRegs]
    · funext i; fin_cases i <;> simp [data, StackRoutines.transferStacks]

/-- The counter controls exactly how many scalar frames are decoded. -/
abbrev command : Cmd 3 4 := .seq setPresent (.seq pop (.seq loop transfer))
def program := compiled command 0 2

theorem command_eval (v pr flag : Bool) (rows : List (List Bool)) (rest output : List Bool) :
    Eval command (9 * (rows.map List.length).sum + 6 * rows.length + 6)
      (data v pr flag (MatrixProgramSupport.words rows ++ rest) [] output
        (List.replicate rows.length true))
      (data false false false rest [] (rows.flatten ++ output) []) := by
  have h1 := setPresent_eval v pr flag (MatrixProgramSupport.words rows ++ rest) [] output
    (List.replicate rows.length true)
  have h2 := pop_eval v true flag (MatrixProgramSupport.words rows ++ rest) [] output
    (List.replicate rows.length true)
  have h3 := loop_eval rows rest [] output
  simp only [List.append_nil] at h3
  have h4 := transfer_eval false true false rest rows.flatten.reverse output []
  simp only [List.reverse_reverse] at h4
  have he := h1.seq (h2.seq (h3.seq h4))
  convert he using 1
  simp [List.length_flatten]
  omega

theorem program_trace (v pr flag : Bool) (rows : List (List Bool)) (rest output : List Bool) :
    Trace program (9 * (rows.map List.length).sum + 6 * rows.length + 7)
      ((data v pr flag (MatrixProgramSupport.words rows ++ rest) [] output
        (List.replicate rows.length true)).withPC (some program.entry))
      ((data false false false rest [] (rows.flatten ++ output) []).withPC none) := by
  have hn : 9 * (rows.map List.length).sum + 6 * rows.length + 7 =
      (9 * (rows.map List.length).sum + 6 * rows.length + 6) + 1 := by
    omega
  rw [hn]
  exact compiled_halt_trace (command_eval v pr flag rows rest output) 0 2

end SubexponentialSAT.Subexp.ScalarBankProgram

end OAI.Algorithms
