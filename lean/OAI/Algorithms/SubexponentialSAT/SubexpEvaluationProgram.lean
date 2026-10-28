import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPostfixGlobal
import OAI.Algorithms.SubexponentialSAT.StackRoutines
import OAI.Algorithms.SubexponentialSAT.StructuredProgram

namespace OAI.Algorithms

/-!
# Concrete evaluation-result extraction

The extractor removes the singleton operand-list framing, parses the result
payload into a reversed scratch stack, and transfers it to physical stack 15.
It clears the operand/depth/scratch stacks and preserves every other stack.
-/

namespace SubexponentialSAT.SubexpEvaluationProgram

open BitProgram
open SubexpPostfixControl

abbrev registers (v p op : Bool) : Fin 16 → Bool :=
  Fin.addCases (motive := fun _ : Fin (3 + 13) => Bool)
    (triple v p op) (fun _ : Fin 13 => false)

abbrev window (frame : Fin 128 → List Bool) (operand depth scratch output : List Bool) :
    Fin 128 → List Bool :=
  Function.update (Function.update (Function.update (Function.update frame 27 operand)
    28 depth) 29 scratch) 15 output

@[simp] theorem window_27 (frame : Fin 128 → List Bool) (a b c d : List Bool) :
    window frame a b c d 27 = a := by simp [window]
@[simp] theorem window_28 (frame : Fin 128 → List Bool) (a b c d : List Bool) :
    window frame a b c d 28 = b := by simp [window]
@[simp] theorem window_29 (frame : Fin 128 → List Bool) (a b c d : List Bool) :
    window frame a b c d 29 = c := by simp [window]
@[simp] theorem window_15 (frame : Fin 128 → List Bool) (a b c d : List Bool) :
    window frame a b c d 15 = d := by simp [window]

@[simp] theorem window_update27 (frame : Fin 128 → List Bool) (a b c d e : List Bool) :
    Function.update (window frame a b c d) 27 e = window frame e b c d := by
  funext i
  by_cases h15 : i = 15 <;> by_cases h27 : i = 27 <;>
    by_cases h28 : i = 28 <;> by_cases h29 : i = 29 <;> simp_all [window, Function.update]
@[simp] theorem window_update28 (frame : Fin 128 → List Bool) (a b c d e : List Bool) :
    Function.update (window frame a b c d) 28 e = window frame a e c d := by
  funext i
  by_cases h15 : i = 15 <;> by_cases h27 : i = 27 <;>
    by_cases h28 : i = 28 <;> by_cases h29 : i = 29 <;> simp_all [window, Function.update]
@[simp] theorem window_update29 (frame : Fin 128 → List Bool) (a b c d e : List Bool) :
    Function.update (window frame a b c d) 29 e = window frame a b e d := by
  funext i
  by_cases h15 : i = 15 <;> by_cases h27 : i = 27 <;>
    by_cases h28 : i = 28 <;> by_cases h29 : i = 29 <;> simp_all [window, Function.update]
@[simp] theorem window_update15 (frame : Fin 128 → List Bool) (a b c d e : List Bool) :
    Function.update (window frame a b c d) 15 e = window frame a b c e := by
  simp [window]

@[simp] theorem registers_zero (v p op : Bool) : registers v p op 0 = v := rfl
@[simp] theorem registers_one (v p op : Bool) : registers v p op 1 = p := rfl
@[simp] theorem registers_two (v p op : Bool) : registers v p op 2 = op := rfl
@[simp] theorem registers_update0 (v p op b : Bool) :
    Function.update (registers v p op) 0 b = registers b p op := by
  funext i
  fin_cases i <;> simp [registers, Function.update, triple, Fin.addCases]
@[simp] theorem registers_update1 (v p op b : Bool) :
    Function.update (registers v p op) 1 b = registers v b op := by
  funext i
  fin_cases i <;> simp [registers, Function.update, triple, Fin.addCases]
@[simp] theorem registers_update2 (v p op b : Bool) :
    Function.update (registers v p op) 2 b = registers v p b := by
  funext i
  fin_cases i <;> simp [registers, Function.update, triple, Fin.addCases]

abbrev ecfg {l : ℕ} (pc : Option (Fin l)) (v p op : Bool) (frame : Fin 128 → List Bool)
    (operand depth scratch output : List Bool) : Cfg 16 128 l :=
  ⟨pc, registers v p op, window frame operand depth scratch output⟩

def parserRegister : Fin 2 → Fin 16 := Fin.castAdd 14
def parserStack (i : Fin 2) : Fin 128 := if i = 0 then 27 else 29
def parserLabel (i : Fin 7) : Fin 17 := Fin.natAdd 3 (Fin.castAdd 7 i)

def extractProgram : Program 16 128 17 where
  inputStack := 27
  outputStack := 15
  entry := 0
  code := Fin.addCases (motive := fun _ : Fin (3 + (7 + 7)) => Instr 16 128 17)
    (fun i : Fin 3 => match i.val with
      | 0 => .pop 15 0 1 1
      | 1 => .branch 1 0 2
      | _ => .pop 27 0 1 3)
    (Fin.addCases (motive := fun _ : Fin (7 + 7) => Instr 16 128 17)
      (fun i : Fin 7 => ProgramLinking.relocateInstr parserRegister parserStack parserLabel
        (some 10) (ParserProgram.frameProgram.code i))
      (fun i : Fin 7 => match i.val with
        | 0 => .pop 27 0 1 11
        | 1 => .pop 28 0 1 12
        | 2 => .set 2 false 13
        | 3 => .pop 29 0 1 14
        | 4 => .branch 1 15 16
        | 5 => .push 15 0 13
        | _ => .halt))

@[simp] private theorem code0 : extractProgram.code 0 = .pop 15 0 1 1 := rfl
@[simp] private theorem code1 : extractProgram.code 1 = .branch 1 0 2 := rfl
@[simp] private theorem code2 : extractProgram.code 2 = .pop 27 0 1 3 := rfl
@[simp] private theorem code10 : extractProgram.code 10 = .pop 27 0 1 11 := rfl
@[simp] private theorem code11 : extractProgram.code 11 = .pop 28 0 1 12 := rfl
@[simp] private theorem code12 : extractProgram.code 12 = .set 2 false 13 := rfl
@[simp] private theorem code13 : extractProgram.code 13 = .pop 29 0 1 14 := rfl
@[simp] private theorem code14 : extractProgram.code 14 = .branch 1 15 16 := rfl
@[simp] private theorem code15 : extractProgram.code 15 = .push 15 0 13 := rfl
@[simp] private theorem code16 : extractProgram.code 16 = .halt := rfl

theorem parserRegister_injective : Function.Injective parserRegister :=
  SubexpPostfixInterpreter.castAdd_injective 2 14
theorem parserStack_injective : Function.Injective parserStack := by decide

theorem parser_code : ProgramLinking.CodeEmbedding ParserProgram.frameProgram extractProgram
    parserRegister parserStack parserLabel (some 10) := by
  intro pc
  simp [extractProgram, parserLabel]

private theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

theorem embed_parser (pc : Option (Fin 7)) (v p op : Bool) (frame : Fin 128 → List Bool)
    (operand depth scratch output : List Bool) :
    ProgramLinking.embedCfg parserRegister parserStack parserLabel (some 10)
      (ecfg none false false op frame [] depth [] output)
      (ParserProgram.cfg pc v p operand scratch) =
    ecfg (ProgramLinking.relocatePc parserLabel (some 10) pc) v p op frame operand depth scratch output := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i
    · change Function.extend parserRegister (ParserProgram.pair v p) _ (parserRegister 0) = v
      rw [parserRegister_injective.extend_apply]
      rfl
    · change Function.extend parserRegister (ParserProgram.pair v p) _ (parserRegister 1) = p
      rw [parserRegister_injective.extend_apply]
      rfl
    all_goals
      change Function.extend parserRegister (ParserProgram.pair v p) _ _ = _
      rw [Function.extend_apply' _ _ _ (by decide)]
      rfl
  · funext i
    by_cases h27 : i = 27
    · subst i
      change Function.extend parserStack (ParserProgram.pair operand scratch) _ (parserStack 0) = _
      rw [parserStack_injective.extend_apply]
      simp [ ParserProgram.pair]
    by_cases h29 : i = 29
    · subst i
      change Function.extend parserStack (ParserProgram.pair operand scratch) _ (parserStack 1) = _
      rw [parserStack_injective.extend_apply]
      simp [ ParserProgram.pair]
    have hn : ¬ ∃ j, parserStack j = i := by
      rintro ⟨j, hj⟩
      fin_cases j
      · exact h27 hj.symm
      · exact h29 hj.symm
    change Function.extend parserStack (ParserProgram.pair operand scratch) _ i = _
    rw [Function.extend_apply' _ _ _ hn]
    simp [ window, Function.update, h27, h29]

theorem parse_trace (bits rest depth output : List Bool) (v p op : Bool)
    (frame : Fin 128 → List Bool) :
    Trace extractProgram (6 * bits.length + 4)
      (ecfg (some 3) v p op frame (Encoding.frame bits ++ rest) depth [] output)
      (ecfg (some 10) false true op frame rest depth bits.reverse output) := by
  have h := ProgramLinking.relocate_trace ParserProgram.frameProgram extractProgram
    parserRegister parserStack parserLabel (some 10)
    (ecfg none false false op frame [] depth [] output)
    parserRegister_injective parserStack_injective parser_code
    (ParserProgram.frame_trace bits rest [] v p)
  rw [embed_parser, embed_parser] at h
  have hlabel : parserLabel 0 = (3 : Fin 17) := by
    apply Fin.ext
    rfl
  simpa only [List.append_nil, ProgramLinking.relocatePc, hlabel] using h

theorem clear_output_trace (operand depth scratch output : List Bool) (v p op : Bool)
    (frame : Fin 128 → List Bool) :
    Trace extractProgram (2 * output.length + 2)
      (ecfg (some 0) v p op frame operand depth scratch output)
      (ecfg (some 2) false false op frame operand depth scratch []) := by
  have h := StackRoutines.clear_trace extractProgram 15 0 1 0 1 2 rfl rfl
    (registers v p op) (window frame operand depth scratch output)
  simpa only [window_15, StackRoutines.clearResult, StackRoutines.clearStacks, readRegs,
    Option.getD_none, Option.isSome_none, registers_update0, registers_update1,
    window_update15, ecfg] using h

theorem transfer_trace (bits : List Bool) (frame : Fin 128 → List Bool) :
    Trace extractProgram (3 * bits.length + 2)
      (ecfg (some 13) true true false frame [] [] bits.reverse [])
      (ecfg (some 16) false false false frame [] [] [] bits) := by
  have h := StackRoutines.transfer_trace extractProgram 29 15 0 1 13 14 15 16
    (by decide) (by decide) rfl rfl rfl (registers true true false) (window frame [] [] bits.reverse [])
  simpa only [window_29, window_15, List.length_reverse, StackRoutines.transferResult,
    StackRoutines.transferStacks, readRegs, Option.getD_none, Option.isSome_none,
    registers_update0, registers_update1, window_update29, window_update15,
    List.reverse_reverse, List.append_nil, ecfg] using h

/-- Actual singleton decoding, including clearing the old destination. -/
theorem extract_trace (bits output : List Bool) (v p op : Bool) (frame : Fin 128 → List Bool) :
    Trace extractProgram (2 * output.length + 9 * bits.length + 13)
      (ecfg (some 0) v p op frame (true :: (Encoding.frame bits ++ [false])) [true] [] output)
      (ecfg none false false false frame [] [] [] bits) := by
  have hc := clear_output_trace (true :: (Encoding.frame bits ++ [false])) [true] [] output v p op frame
  have hp : Trace extractProgram 1
      (ecfg (some 2) false false op frame (true :: (Encoding.frame bits ++ [false])) [true] [] [])
      (ecfg (some 3) true true op frame (Encoding.frame bits ++ [false]) [true] [] []) := by
    refine .cons ?_ (.refl _)
    simp [step, execInstr, ecfg, readRegs]
  have hparse := parse_trace bits [false] [true] [] true true op frame
  have hs : Trace extractProgram 3
      (ecfg (some 10) false true op frame [false] [true] bits.reverse [])
      (ecfg (some 13) true true false frame [] [] bits.reverse []) := by
    refine .cons (b := ecfg (some 11) false true op frame [] [true] bits.reverse []) ?_ ?_
    · simp [step, execInstr, ecfg, readRegs]
    refine .cons (b := ecfg (some 12) true true op frame [] [] bits.reverse []) ?_ ?_
    · simp [step, execInstr, ecfg, readRegs]
    refine .cons ?_ (.refl _)
    simp [step, execInstr, ecfg]
  have ht := transfer_trace bits frame
  have hh : Trace extractProgram 1
      (ecfg (some 16) false false false frame [] [] [] bits)
      (ecfg none false false false frame [] [] [] bits) := by
    refine .cons ?_ (.refl _)
    simp [step, execInstr, ecfg]
  have h := ((((hc.trans hp).trans hparse).trans hs).trans ht).trans hh
  have hn : 2 * output.length + 2 + 1 + (6 * bits.length + 4) + 3 +
      (3 * bits.length + 2) + 1 = 2 * output.length + 9 * bits.length + 13 := by omega
  simpa only [hn] using h

theorem window_preserves (frame : Fin 128 → List Bool) (a b c d : List Bool)
    (i : Fin 128) (h15 : i ≠ 15) (h27 : i ≠ 27) (h28 : i ≠ 28) (h29 : i ≠ 29) :
    window frame a b c d i = frame i := by simp [window, h15, h27, h28, h29]

theorem window_self (frame : Fin 128 → List Bool) :
    window frame (frame 27) (frame 28) (frame 29) (frame 15) = frame := by
  simp [window]

open SubexpPostfixGlobal

/-- The interpreter's final stack contents before the framing is removed. -/
def snapshot (bits : List Bool) (context : Fin 124 → List Bool) : Fin 128 → List Bool :=
  (physicalCfg (l := 1) none false false false [] [true]
    (true :: (Encoding.frame bits ++ [false])) context).stacks

@[simp] theorem snapshot_operand (bits : List Bool) (context : Fin 124 → List Bool) :
    snapshot bits context 27 = true :: (Encoding.frame bits ++ [false]) :=
  physicalCfg_operands _ _ _ _ _ _ _ _
@[simp] theorem snapshot_depth (bits : List Bool) (context : Fin 124 → List Bool) :
    snapshot bits context 28 = [true] := physicalCfg_depth _ _ _ _ _ _ _ _
@[simp] theorem snapshot_scratch (bits : List Bool) (context : Fin 124 → List Bool) :
    snapshot bits context 29 = [] := physicalCfg_scratch _ _ _ _ _ _ _ _
@[simp] theorem snapshot_output (bits : List Bool) (context : Fin 124 → List Bool) :
    snapshot bits context 15 = context 11 := rfl

theorem physical_result_ecfg {l : ℕ} (pc : Option (Fin l)) (bits : List Bool)
    (op : Bool) (context : Fin 124 → List Bool) :
    physicalCfg pc false false op [] [true] (true :: (Encoding.frame bits ++ [false])) context =
      ecfg pc false false op (snapshot bits context)
        (true :: (Encoding.frame bits ++ [false])) [true] [] (context 11) := by
  apply cfg_ext
  · rfl
  · rfl
  · change snapshot bits context = window (snapshot bits context)
      (true :: (Encoding.frame bits ++ [false])) [true] [] (context 11)
    simpa only [snapshot_operand, snapshot_depth, snapshot_scratch, snapshot_output] using
      (window_self (snapshot bits context)).symm

abbrev evaluationProgram {a b : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b) :
    Program 16 128 ((37 + (2 + (a + b))) + 17) :=
  ProgramLinking.link (globalProgram add mul) extractProgram

/-- A concrete evaluation/extraction service for the shared moment machine.
The final payload is forward on stack 15, and stacks 27, 28, 29 are empty. -/
theorem evaluation_runsIn {R : Type*} [Add R] [Mul R] {a b : ℕ}
    (add : Program 16 128 a) (mul : Program 16 128 b) (encode : R → List Bool)
    (addBound mulBound : R → R → ℕ) (context : Fin 124 → List Bool)
    (ha : ImplementsGlobal encode (· + ·) false add addBound context)
    (hm : ImplementsGlobal encode (· * ·) true mul mulBound context) (e : Algorithm.Expr R) :
    RunsIn (evaluationProgram add mul)
      (e.cost (SubexpPostfixInterpreter.costs encode addBound mulBound) +
        2 * (context 11).length + 9 * (encode e.eval).length + 18)
      (physicalCfg (some (evaluationProgram add mul).entry) false false false
        (serializeCode encode e.compile) [] [] context)
      (ecfg none false false false (snapshot (encode e.eval) context) [] [] [] (encode e.eval)) := by
  obtain ⟨op, he⟩ := global_complete_runsIn add mul encode addBound mulBound context ha hm e
  have hx : RunsIn extractProgram (2 * (context 11).length + 9 * (encode e.eval).length + 13)
      (ProgramLinking.enter extractProgram
        (physicalCfg (l := 37 + (2 + (a + b))) none false false op [] (operandDepth [e.eval])
          (Encoding.encodeList encode [e.eval]) context))
      (ecfg none false false false (snapshot (encode e.eval) context) [] [] [] (encode e.eval)) := by
    refine ⟨_, le_rfl, ?_⟩
    have h := extract_trace (encode e.eval) (context 11) false false op (snapshot (encode e.eval) context)
    have hp := physical_result_ecfg (l := 17) (some 0) (encode e.eval) op context
    change Trace extractProgram _
      (physicalCfg (some 0) false false op [] [true]
        (true :: (Encoding.frame (encode e.eval) ++ [false])) context) _
    rw [hp]
    exact h
  have h := ProgramLinking.link_runsIn (globalProgram add mul) extractProgram he rfl hx
  change RunsIn (evaluationProgram add mul) _
    (physicalCfg (some (evaluationProgram add mul).entry) false false false
      (serializeCode encode e.compile) [] [] context)
    (ecfg none false false false (snapshot (encode e.eval) context) [] [] [] (encode e.eval)) at h
  convert h using 1
  omega

@[simp] theorem evaluation_output {l : ℕ} (bits : List Bool) (context : Fin 124 → List Bool) :
    (ecfg (l := l) none false false false (snapshot bits context) [] [] [] bits).stacks 15 = bits := by
  simp []

theorem evaluation_result_layout {l : ℕ} (bits : List Bool) (context : Fin 124 → List Bool) :
    let out := ecfg (l := l) none false false false (snapshot bits context) [] [] [] bits
    out.stacks 26 = [] ∧ out.stacks 27 = [] ∧ out.stacks 28 = [] ∧ out.stacks 29 = [] ∧
      out.regs = fun _ => false := by
  dsimp only
  refine ⟨?_, by simp [], by simp [], by simp [], ?_⟩
  · simp [ window, snapshot]
  · funext i
    fin_cases i <;> rfl

theorem physical_high_stack {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) (i : Fin 28) :
    (physicalCfg pc v p op code depth operands context).stacks ⟨100 + i.val, by omega⟩ =
      context ⟨96 + i.val, by omega⟩ := by
  fin_cases i <;> rfl

/-- All twenty-eight caller-persistent stacks are unchanged. -/
theorem evaluation_preserves_caller {l : ℕ} (bits : List Bool) (context : Fin 124 → List Bool)
    (i : Fin 28) :
    (ecfg (l := l) none false false false (snapshot bits context) [] [] [] bits).stacks
      ⟨100 + i.val, by omega⟩ = context ⟨96 + i.val, by omega⟩ := by
  change window _ _ _ _ _ _ = _
  rw [window_preserves _ _ _ _ _ _ (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega)]
  exact physical_high_stack _ _ _ _ _ _ _ _ i

/-! ## Entry from arbitrary caller registers -/

def resetList : List (Fin 16) → StructuredProgram.Cmd 16 128
  | [] => .skip
  | i :: is => .seq (.atom (.set i false)) (resetList is)

def resetData (is : List (Fin 16)) (d : StructuredProgram.State 16 128) :
    StructuredProgram.State 16 128 :=
  ⟨fun i => if i ∈ is then false else d.regs i, d.stacks⟩

theorem resetList_eval (is : List (Fin 16)) (d : StructuredProgram.State 16 128) :
    StructuredProgram.Eval (resetList is) is.length d (resetData is d) := by
  induction is generalizing d with
  | nil => simpa [resetList, resetData] using StructuredProgram.Eval.skip d
  | cons i is ih =>
      have h := StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.set i false) d)
        (ih ((StructuredProgram.Atom.set i false).eval d))
      have hd : resetData is ((StructuredProgram.Atom.set i false).eval d) = resetData (i :: is) d := by
        apply congrArg₂ StructuredProgram.State.mk
        · funext j
          by_cases hj : j = i <;> by_cases hm : j ∈ is <;>
            simp [ StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
              StructuredProgram.State.ofCfg,
              execInstr, Function.update, hj, hm]
        · rfl
      simpa only [resetList, List.length_cons, hd, Nat.add_comm] using h

abbrev resetProgram : Program 16 128 17 :=
  StructuredProgram.compiled (resetList (List.finRange 16)) 26 15

theorem reset_trace (regs : Fin 16 → Bool) (stk : Fin 128 → List Bool) :
    Trace resetProgram 17 ⟨some resetProgram.entry, regs, stk⟩ ⟨none, fun _ => false, stk⟩ := by
  have h := resetList_eval (List.finRange 16) ⟨regs, stk⟩
  have he : StructuredProgram.Eval (resetList (List.finRange 16)) 16
      ⟨regs, stk⟩ ⟨fun _ => false, stk⟩ := by
    simpa [resetData] using h
  exact StructuredProgram.compiled_halt_trace he 26 15

@[simp] theorem registers_false : registers false false false = fun _ => false := by
  funext i
  fin_cases i <;> rfl

def inputCfg {l : ℕ} (pc : Option (Fin l)) (regs : Fin 16 → Bool)
    (code : List Bool) (context : Fin 124 → List Bool) : Cfg 16 128 l :=
  { physicalCfg pc false false false code [] [] context with regs := regs }

theorem inputCfg_stacks {l : ℕ} (pc : Option (Fin l)) (regs : Fin 16 → Bool)
    (code : List Bool) (context : Fin 124 → List Bool) :
    (inputCfg pc regs code context).stacks = (physicalCfg pc false false false code [] [] context).stacks := rfl

/-- Recover the persistent context from an arbitrary shared-machine frame. -/
def contextOf (stk : Fin 128 → List Bool) : Fin 124 → List Bool :=
  fun i => stk (ports (Fin.natAdd 4 i))

theorem inputCfg_of_stacks {l : ℕ} (pc : Option (Fin l)) (regs : Fin 16 → Bool)
    (code : List Bool) (stk : Fin 128 → List Bool)
    (h26 : stk 26 = code) (h27 : stk 27 = []) (h28 : stk 28 = []) (h29 : stk 29 = []) :
    inputCfg pc regs code (contextOf stk) = ⟨pc, regs, stk⟩ := by
  apply cfg_ext
  · rfl
  · rfl
  · funext i
    obtain ⟨j, rfl⟩ := ports.surjective i
    refine Fin.addCases (m := 4) (n := 124) ?_ ?_ j
    · intro k
      fin_cases k
      · change code = stk 26
        exact h26.symm
      · change ([] : List Bool) = stk 28
        exact h28.symm
      · change ([] : List Bool) = stk 27
        exact h27.symm
      · change ([] : List Bool) = stk 29
        exact h29.symm
    · intro k
      rw [inputCfg_stacks, physicalCfg_context]
      rfl

/-- This ready-to-call service first clears all sixteen registers by concrete
instructions, so caller loop flags need no special precondition. -/
abbrev readyEvaluationProgram {a b : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b) :
    Program 16 128 (17 + ((37 + (2 + (a + b))) + 17)) :=
  ProgramLinking.link resetProgram (evaluationProgram add mul)

theorem ready_evaluation_runsIn {R : Type*} [Add R] [Mul R] {a b : ℕ}
    (add : Program 16 128 a) (mul : Program 16 128 b) (encode : R → List Bool)
    (addBound mulBound : R → R → ℕ) (context : Fin 124 → List Bool)
    (ha : ImplementsGlobal encode (· + ·) false add addBound context)
    (hm : ImplementsGlobal encode (· * ·) true mul mulBound context)
    (e : Algorithm.Expr R) (regs : Fin 16 → Bool) :
    RunsIn (readyEvaluationProgram add mul)
      (e.cost (SubexpPostfixInterpreter.costs encode addBound mulBound) +
        2 * (context 11).length + 9 * (encode e.eval).length + 35)
      (inputCfg (some (readyEvaluationProgram add mul).entry) regs
        (serializeCode encode e.compile) context)
      (ecfg none false false false (snapshot (encode e.eval) context) [] [] [] (encode e.eval)) := by
  let code := serializeCode encode e.compile
  have hr : Trace resetProgram 17
      (inputCfg (some resetProgram.entry) regs code context)
      (physicalCfg none false false false code [] [] context) := by
    change Trace resetProgram 17
      ⟨some resetProgram.entry, regs, _⟩ ⟨none, registers false false false, _⟩
    rw [registers_false]
    exact reset_trace regs _
  have hrr : RunsIn resetProgram 17
      (inputCfg (some resetProgram.entry) regs code context)
      (physicalCfg none false false false code [] [] context) := ⟨17, le_rfl, hr⟩
  have he := evaluation_runsIn add mul encode addBound mulBound context ha hm e
  have h := ProgramLinking.link_runsIn resetProgram (evaluationProgram add mul) hrr rfl he
  change RunsIn (readyEvaluationProgram add mul) _
    (inputCfg (some (readyEvaluationProgram add mul).entry) regs code context)
    (ecfg none false false false (snapshot (encode e.eval) context) [] [] [] (encode e.eval)) at h
  convert h using 1
  omega

/-- State-level entry contract: only the source bytes and three empty work
stacks are prescribed; the rest of the shared frame is recovered explicitly. -/
theorem ready_evaluation_state_runsIn {R : Type*} [Add R] [Mul R] {a b : ℕ}
    (add : Program 16 128 a) (mul : Program 16 128 b) (encode : R → List Bool)
    (addBound mulBound : R → R → ℕ) (e : Algorithm.Expr R)
    (regs : Fin 16 → Bool) (stk : Fin 128 → List Bool)
    (h26 : stk 26 = serializeCode encode e.compile)
    (h27 : stk 27 = []) (h28 : stk 28 = []) (h29 : stk 29 = [])
    (ha : ImplementsGlobal encode (· + ·) false add addBound (contextOf stk))
    (hm : ImplementsGlobal encode (· * ·) true mul mulBound (contextOf stk)) :
    RunsIn (readyEvaluationProgram add mul)
      (e.cost (SubexpPostfixInterpreter.costs encode addBound mulBound) +
        2 * ((contextOf stk) 11).length + 9 * (encode e.eval).length + 35)
      ⟨some (readyEvaluationProgram add mul).entry, regs, stk⟩
      (ecfg none false false false (snapshot (encode e.eval) (contextOf stk)) [] [] [] (encode e.eval)) := by
  have h := ready_evaluation_runsIn add mul encode addBound mulBound (contextOf stk) ha hm e regs
  rw [inputCfg_of_stacks _ _ _ _ h26 h27 h28 h29] at h
  exact h

end SubexponentialSAT.SubexpEvaluationProgram

end OAI.Algorithms
