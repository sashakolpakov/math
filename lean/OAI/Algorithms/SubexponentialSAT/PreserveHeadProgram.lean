import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFRecords
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Bounded head-record extraction with source preservation

Only the first tagged frame is traversed. A concrete fanout loop restores
the captured record onto the untouched source tail and produces a bounded
copy for parsing. The running time is independent of the tail length.
-/

namespace SubexponentialSAT.PreserveHeadProgram

open BitProgram StructuredCalls

abbrev Data := State 2 5

abbrev state (v p : Bool) (source output scratch copy extra : List Bool) : Data :=
  ⟨ParserProgram.pair v p, ![source, output, scratch, copy, extra]⟩

@[simp] theorem update_five_zero {α : Type*} (a b c d e x : α) :
    Function.update ![a, b, c, d, e] 0 x = ![x, b, c, d, e] := by
  funext i
  fin_cases i <;> simp

@[simp] theorem update_five_one {α : Type*} (a b c d e x : α) :
    Function.update ![a, b, c, d, e] 1 x = ![a, x, c, d, e] := by
  funext i
  fin_cases i <;> simp

@[simp] theorem update_five_two {α : Type*} (a b c d e x : α) :
    Function.update ![a, b, c, d, e] 2 x = ![a, b, x, d, e] := by
  funext i
  fin_cases i <;> simp

@[simp] theorem update_five_three {α : Type*} (a b c d e x : α) :
    Function.update ![a, b, c, d, e] 3 x = ![a, b, c, x, e] := by
  funext i
  fin_cases i <;> simp

def record (bits : List Bool) : List Bool := true :: Encoding.frame bits
def pending (bits tail : List Bool) : List Bool := true :: (Encoding.frame bits ++ tail)

def captureStack (i : Fin 3) : Fin 5 := i.castAdd 2
theorem captureStack_injective : Function.Injective captureStack := Fin.castAdd_injective 3 2

abbrev capture : Cmd 2 5 := .call (ProgramLinking.liftProgram
  ExecCNFRecords.captureProgram id captureStack)

private theorem embed_capture (v₀ p₀ v p : Bool)
    (source₀ output₀ scratch₀ source output scratch copy extra : List Bool) :
    embedState id captureStack (state v₀ p₀ source₀ output₀ scratch₀ copy extra)
      (⟨ParserProgram.pair v p, ExecCNFRecords.ports source output scratch⟩ : State 2 3) =
      state v p source output scratch copy extra := by
  apply embedState_eq_of_ports id captureStack _ _ _ Function.injective_id captureStack_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> first
      | rfl
      | exact (hi ⟨0, rfl⟩).elim
      | exact (hi ⟨1, rfl⟩).elim
      | exact (hi ⟨2, rfl⟩).elim

theorem capture_eval (bits tail extra : List Bool) (v p : Bool) :
    Eval capture (7 * bits.length + 9)
      (state v p (pending bits tail) [] [] [] extra)
      (state false true tail [] (record bits).reverse [] extra) := by
  have ht := ExecCNFRecords.capture_record_trace bits tail [] [] v p
  simp only [List.append_nil] at ht
  change Trace ExecCNFRecords.captureProgram (7 * bits.length + 9)
    ((⟨ParserProgram.pair v p, ExecCNFRecords.ports (pending bits tail) [] []⟩ : State 2 3).withPC
      (some ExecCNFRecords.captureProgram.entry))
    ((⟨ParserProgram.pair false true, ExecCNFRecords.ports tail [] (record bits).reverse⟩ : State 2 3).withPC none) at ht
  have he := eval_call_lifted ExecCNFRecords.captureProgram id captureStack
    (state v p (pending bits tail) [] [] [] extra) Function.injective_id captureStack_injective ht
  simpa only [capture, embed_capture, record, pending] using he

/-- Four primitive instructions copy each captured bit onto both destinations. -/
abbrev fanoutProgram : Program 2 5 5 where
  inputStack := 2
  outputStack := 3
  entry := 0
  code := ![.pop 2 0 1 1, .branch 1 2 4, .push 0 0 3, .push 3 0 0, .halt]

abbrev fanout : Cmd 2 5 := .call fanoutProgram

theorem fanout_eval (word tail extra : List Bool) (v p : Bool) :
    Eval fanout (4 * word.length + 3)
      (state v p tail [] word.reverse [] extra)
      (state false false (word ++ tail) [] [] word extra) := by
  have ht := StackRoutines.fanout_trace fanoutProgram 2 0 3 0 1 0 1 2 3 4
    (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl
    (ParserProgram.pair v p) (state v p tail [] word.reverse [] extra).stacks
  have hh := StackRoutines.halt_after_trace fanoutProgram ht 4 rfl rfl
  apply Eval.call
  simpa [state, StackRoutines.fanoutResult, StackRoutines.fanoutStacks,
    StructuredProgram.State.withPC, readRegs, Nat.add_assoc] using hh

abbrev dropTag : Cmd 2 5 := .base (.atom (.pop 3 0 1))

theorem dropTag_eval (bits source extra : List Bool) (v p : Bool) :
    Eval dropTag 1 (state v p source [] [] (record bits) extra)
      (state true true source [] [] (Encoding.frame bits) extra) := by
  apply Eval.base
  simpa [dropTag, state, record, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr, readRegs] using
    StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 2) (s := 5) 3 0 1)
      (state v p source [] [] (record bits) extra)

def parseStack : Fin 2 → Fin 5 := ![3, 2]
theorem parseStack_injective : Function.Injective parseStack := by decide
abbrev parse : Cmd 2 5 := .call (ProgramLinking.liftProgram ParserProgram.frameProgram id parseStack)

private theorem embed_parse (v₀ p₀ v p : Bool)
    (source output scratch₀ copy₀ input result extra : List Bool) :
    embedState id parseStack (state v₀ p₀ source output scratch₀ copy₀ extra)
      (⟨ParserProgram.pair v p, ParserProgram.pair input result⟩ : State 2 2) =
      state v p source output result input extra := by
  apply embedState_eq_of_ports id parseStack _ _ _ Function.injective_id parseStack_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> first
      | rfl
      | exact (hi ⟨0, rfl⟩).elim
      | exact (hi ⟨1, rfl⟩).elim

theorem parse_eval (bits source extra : List Bool) (v p : Bool) :
    Eval parse (6 * bits.length + 4)
      (state v p source [] [] (Encoding.frame bits) extra)
      (state false true source [] bits.reverse [] extra) := by
  have ht := ParserProgram.frame_trace bits [] [] v p
  simp only [List.append_nil] at ht
  change Trace ParserProgram.frameProgram (6 * bits.length + 4)
    ((⟨ParserProgram.pair v p, ParserProgram.pair (Encoding.frame bits) []⟩ : State 2 2).withPC
      (some ParserProgram.frameProgram.entry))
    ((⟨ParserProgram.pair false true, ParserProgram.pair [] bits.reverse⟩ : State 2 2).withPC none) at ht
  have he := eval_call_lifted ParserProgram.frameProgram id parseStack
    (state v p source [] [] (Encoding.frame bits) extra) Function.injective_id parseStack_injective ht
  simpa only [parse, embed_parse] using he

abbrev restore : Cmd 2 5 := .call (StackRoutines.transferProgram 2 1 0 1)

theorem restore_eval (bits source extra : List Bool) (v p : Bool) :
    Eval restore (3 * bits.length + 3)
      (state v p source [] bits.reverse [] extra)
      (state false false source bits [] [] extra) := by
  have ht := ListRegisterProgram.transfer_run (r := 2) (s := 5)
    2 1 0 1 (by decide) (by decide) (ParserProgram.pair v p)
    (state v p source [] bits.reverse [] extra).stacks
  apply Eval.call
  simpa [ListRegisterProgram.Run, state, StructuredProgram.State.withPC,
    StackRoutines.transferStacks, readRegs] using ht

abbrev command : Cmd 2 5 := .seq capture (.seq fanout (.seq dropTag (.seq parse restore)))

/-- The arbitrary tail and unused fifth stack are preserved exactly. -/
theorem command_eval (bits tail extra : List Bool) (v p : Bool) :
    Eval command (24 * bits.length + 28)
      (state v p (pending bits tail) [] [] [] extra)
      (state false false (pending bits tail) bits [] [] extra) := by
  have he := (capture_eval bits tail extra v p).seq
    ((fanout_eval (record bits) tail extra false true).seq
      ((dropTag_eval bits (record bits ++ tail) extra false false).seq
        ((parse_eval bits (record bits ++ tail) extra true true).seq
          (restore_eval bits (record bits ++ tail) extra false true))))
  have ht : (7 * bits.length + 9) + ((4 * (record bits).length + 3) +
      (1 + ((6 * bits.length + 4) + (3 * bits.length + 3)))) = 24 * bits.length + 28 := by
    simp only [record, List.length_cons, Encoding.length_frame]
    omega
  rw [ht] at he
  simpa only [command, record, pending, List.cons_append] using he

abbrev program := compiled command 0 1

theorem program_trace (bits tail extra : List Bool) (v p : Bool) :
    Trace program (24 * bits.length + 29)
      ((state v p (pending bits tail) [] [] [] extra).withPC (some program.entry))
      ((state false false (pending bits tail) bits [] [] extra).withPC none) := by
  have ht := compiled_halt_trace (command_eval bits tail extra v p) 0 1
  simpa only [Nat.add_assoc] using ht

theorem primitive_execution (bits tail extra : List Bool) (v p : Bool) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (24 * bits.length + 29))
      (primitiveCfg program ((state v p (pending bits tail) [] [] [] extra).withPC (some program.entry)))
      (primitiveCfg program ((state false false (pending bits tail) bits [] [] extra).withPC none)) :=
  BitProgram.primitive_trace program (program_trace bits tail extra v p)

noncomputable def liftedResult {r s : ℕ} (reg : Fin 2 → Fin r) (stk : Fin 5 → Fin s)
    (frame : State r s) (bits tail : List Bool) : State r s :=
  embedState reg stk frame (state false false (pending bits tail) bits [] [] (frame.stacks (stk 4)))

/-- A larger fixed caller may choose arbitrary injective ports. Only the two
selected registers and four active stack ports can change. -/
theorem lifted_run {r s : ℕ} (reg : Fin 2 → Fin r) (stk : Fin 5 → Fin s)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame : State r s) (bits tail : List Bool)
    (h0 : frame.stacks (stk 0) = pending bits tail)
    (h1 : frame.stacks (stk 1) = []) (h2 : frame.stacks (stk 2) = [])
    (h3 : frame.stacks (stk 3) = []) :
    Eval (.call (ProgramLinking.liftProgram program reg stk)) (24 * bits.length + 29)
      frame (liftedResult reg stk frame bits tail) := by
  have ht := program_trace bits tail (frame.stacks (stk 4)) (frame.regs (reg 0)) (frame.regs (reg 1))
  have he := eval_call_lifted program reg stk frame hr hs ht
  have hi : embedState reg stk frame
      (state (frame.regs (reg 0)) (frame.regs (reg 1)) (pending bits tail) [] [] []
        (frame.stacks (stk 4))) = frame := by
    apply embedState_eq_of_ports reg stk frame frame _ hr hs
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
    · intro i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · rfl
    · intro i hi; rfl
  rw [hi] at he
  exact he

theorem lifted_stack {r s : ℕ} (reg : Fin 2 → Fin r) (stk : Fin 5 → Fin s)
    (hs : Function.Injective stk) (frame : State r s) (bits tail : List Bool) (i : Fin 5) :
    (liftedResult reg stk frame bits tail).stacks (stk i) =
      (state false false (pending bits tail) bits [] [] (frame.stacks (stk 4))).stacks i :=
  embedState_stack _ _ _ _ hs i

theorem lifted_stack_frame {r s : ℕ} (reg : Fin 2 → Fin r) (stk : Fin 5 → Fin s)
    (frame : State r s) (bits tail : List Bool) (i : Fin s) (hi : ¬ ∃ j, stk j = i) :
    (liftedResult reg stk frame bits tail).stacks i = frame.stacks i :=
  embedState_stack_frame _ _ _ _ _ hi

theorem lifted_register_frame {r s : ℕ} (reg : Fin 2 → Fin r) (stk : Fin 5 → Fin s)
    (frame : State r s) (bits tail : List Bool) (i : Fin r) (hi : ¬ ∃ j, reg j = i) :
    (liftedResult reg stk frame bits tail).regs i = frame.regs i :=
  embedState_register_frame _ _ _ _ _ hi

end SubexponentialSAT.PreserveHeadProgram

end OAI.Algorithms
