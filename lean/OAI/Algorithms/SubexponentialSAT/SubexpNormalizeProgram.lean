import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ParserProgram
import OAI.Algorithms.SubexponentialSAT.SubexpFrontend
import OAI.Algorithms.SubexponentialSAT.ExecCNF
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

namespace OAI.Algorithms

/-!
# Concrete syntax routines for CNF normalization

This module begins the machine implementation of normalization with the
complement-query operation used in tautology testing. `negateProgram` is one
fixed finite instruction table. It scans a unary literal code in pairs and
emits the code with its polarity flipped. Unbounded data stays on the stacks.

The theorems count actual `BitProgram.step` transitions. Full formula
deduplication, tautology filtering, and absorption are separate obligations;
this routine is not presented as the completed normalization algorithm.
-/

namespace SubexponentialSAT.SubexpNormalizeProgram

open BitProgram
open ParserProgram (cfg)

/-- A unary code `2*v+b` is transformed into `2*v+(1-b)`. Stack 0 is
input, stack 1 is output, and both Boolean registers are cleared on return.
The output accumulator is preserved as a suffix. -/
abbrev negateProgram : Program 2 2 15 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 0 false 1
    | 1 => .push 1 0 2
    | 2 => .pop 0 0 1 3
    | 3 => .branch 1 4 12
    | 4 => .branch 0 5 10
    | 5 => .pop 0 0 1 6
    | 6 => .branch 1 7 12
    | 7 => .branch 0 8 12
    | 8 => .push 1 0 9
    | 9 => .push 1 0 2
    | 10 => .set 0 true 11
    | 11 => .push 1 0 12
    | 12 => .set 0 false 13
    | 13 => .set 1 false 14
    | _ => .halt

private theorem negate_start (v p : Bool) (input output : List Bool) :
    Trace negateProgram 2 (cfg (some 0) v p input output)
      (cfg (some 2) false p input (false :: output)) := by
  refine .cons (b := cfg (some 1) false p input output) ?_ (.cons ?_ (.refl _)) <;>
    simp [step, cfg, execInstr]

/-- Eight fixed instructions consume one pair of unary marks. -/
theorem negate_pair (v p : Bool) (input output : List Bool) :
    Trace negateProgram 8 (cfg (some 2) v p (true :: true :: input) output)
      (cfg (some 2) true true input (true :: true :: output)) := by
  refine .cons (b := cfg (some 3) true true (true :: input) output) ?_
    (.cons (b := cfg (some 4) true true (true :: input) output) ?_
    (.cons (b := cfg (some 5) true true (true :: input) output) ?_
    (.cons (b := cfg (some 6) true true input output) ?_
    (.cons (b := cfg (some 7) true true input output) ?_
    (.cons (b := cfg (some 8) true true input output) ?_
    (.cons (b := cfg (some 9) true true input (true :: output)) ?_
    (.cons ?_ (.refl _)))))))) <;>
    simp [step, cfg, execInstr, readRegs]

private theorem negate_finish (v p : Bool) (input output : List Bool) :
    Trace negateProgram 3 (cfg (some 12) v p input output)
      (cfg none false false input output) := by
  refine .cons (b := cfg (some 13) false p input output) ?_
    (.cons (b := cfg (some 14) false false input output) ?_
    (.cons ?_ (.refl _))) <;>
    simp [step, cfg, execInstr]

private theorem negate_even_zero (v p : Bool) (input output : List Bool) :
    Trace negateProgram 8 (cfg (some 2) v p (false :: input) output)
      (cfg none false false input (true :: output)) := by
  have h : Trace negateProgram 5 (cfg (some 2) v p (false :: input) output)
      (cfg (some 12) true true input (true :: output)) := by
    refine .cons (b := cfg (some 3) false true input output) ?_
      (.cons (b := cfg (some 4) false true input output) ?_
      (.cons (b := cfg (some 10) false true input output) ?_
      (.cons (b := cfg (some 11) true true input output) ?_
      (.cons ?_ (.refl _))))) <;>
      simp [step, cfg, execInstr, readRegs]
  exact h.trans (negate_finish true true input (true :: output))

private theorem negate_odd_zero (v p : Bool) (input output : List Bool) :
    Trace negateProgram 9 (cfg (some 2) v p (true :: false :: input) output)
      (cfg none false false input output) := by
  have h : Trace negateProgram 6 (cfg (some 2) v p (true :: false :: input) output)
      (cfg (some 12) false true input output) := by
    refine .cons (b := cfg (some 3) true true (false :: input) output) ?_
      (.cons (b := cfg (some 4) true true (false :: input) output) ?_
      (.cons (b := cfg (some 5) true true (false :: input) output) ?_
      (.cons (b := cfg (some 6) false true input output) ?_
      (.cons (b := cfg (some 7) false true input output) ?_
      (.cons ?_ (.refl _)))))) <;>
      simp [step, cfg, execInstr, readRegs]
  exact h.trans (negate_finish false true input output)

private theorem negate_even_loop (n : ℕ) (rest output : List Bool) (v p : Bool) :
    Trace negateProgram (8 * n + 8)
      (cfg (some 2) v p (Encoding.encodeNat (2 * n) ++ rest) output)
      (cfg none false false rest (List.replicate (2 * n + 1) true ++ output)) := by
  induction n generalizing output v p with
  | zero => simpa [Encoding.encodeNat] using negate_even_zero v p rest output
  | succ n ih =>
      have h := (negate_pair v p (Encoding.encodeNat (2 * n) ++ rest) output).trans
        (ih (true :: true :: output) true true)
      have htime : 8 + (8 * n + 8) = 8 * (n + 1) + 8 := by omega
      have hin : Encoding.encodeNat (2 * (n + 1)) ++ rest =
          true :: true :: (Encoding.encodeNat (2 * n) ++ rest) := by
        rw [show 2 * (n + 1) = 2 + 2 * n by omega]
        simp [Encoding.encodeNat, List.replicate_add, List.append_assoc]
      have hout : List.replicate (2 * n + 1) true ++ true :: true :: output =
          List.replicate (2 * (n + 1) + 1) true ++ output := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
        simp [List.replicate_add, List.append_assoc]
      simpa only [htime, hin, hout] using h

private theorem negate_odd_loop (n : ℕ) (rest output : List Bool) (v p : Bool) :
    Trace negateProgram (8 * n + 9)
      (cfg (some 2) v p (Encoding.encodeNat (2 * n + 1) ++ rest) output)
      (cfg none false false rest (List.replicate (2 * n) true ++ output)) := by
  induction n generalizing output v p with
  | zero => simpa [Encoding.encodeNat] using negate_odd_zero v p rest output
  | succ n ih =>
      have h := (negate_pair v p (Encoding.encodeNat (2 * n + 1) ++ rest) output).trans
        (ih (true :: true :: output) true true)
      have htime : 8 + (8 * n + 9) = 8 * (n + 1) + 9 := by omega
      have hin : Encoding.encodeNat (2 * (n + 1) + 1) ++ rest =
          true :: true :: (Encoding.encodeNat (2 * n + 1) ++ rest) := by
        rw [show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by omega]
        simp [Encoding.encodeNat, List.replicate_add, List.append_assoc]
      have hout : List.replicate (2 * n) true ++ true :: true :: output =
          List.replicate (2 * (n + 1)) true ++ output := by
        rw [show 2 * (n + 1) = 2 * n + 2 by omega]
        simp [List.replicate_add, List.append_assoc]
      simpa only [htime, hin, hout] using h

/-- The exact running time depends only on the scanned code length and parity. -/
def negateSteps (c : ℕ) : ℕ := 8 * (c / 2) + 10 + c % 2

/-- Actual execution on a valid encoded literal. The input suffix and output
accumulator are preserved exactly, so this is usable as a linked subroutine. -/
theorem negate_trace (c : ℕ) (rest output : List Bool) (v p : Bool) :
    Trace negateProgram (negateSteps c)
      (cfg (some 0) v p (Encoding.encodeNat c ++ rest) output)
      (cfg none false false rest
        (Encoding.encodeNat (SubexpFrontend.negateCode c) ++ output)) := by
  have hmod : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases hmod with hmod | hmod
  · have hc : c = 2 * (c / 2) := by omega
    have hloop := negate_even_loop (c / 2) rest (false :: output) false p
    rw [← show Encoding.encodeNat c = Encoding.encodeNat (2 * (c / 2)) from
      congrArg Encoding.encodeNat hc] at hloop
    have h := (negate_start v p (Encoding.encodeNat c ++ rest) output).trans
      hloop
    have htime : 2 + (8 * (c / 2) + 8) = 8 * (c / 2) + 10 := by omega
    rw [htime] at h
    simpa [negateSteps, SubexpFrontend.negateCode, hmod, Encoding.encodeNat,
      List.append_assoc, Nat.add_assoc] using h
  · have hc : c = 2 * (c / 2) + 1 := by omega
    have hloop := negate_odd_loop (c / 2) rest (false :: output) false p
    rw [← show Encoding.encodeNat c = Encoding.encodeNat (2 * (c / 2) + 1) from
      congrArg Encoding.encodeNat hc] at hloop
    have h := (negate_start v p (Encoding.encodeNat c ++ rest) output).trans
      hloop
    have htime : 2 + (8 * (c / 2) + 9) = 8 * (c / 2) + 11 := by omega
    rw [htime] at h
    simpa [negateSteps, SubexpFrontend.negateCode, hmod, Encoding.encodeNat,
      List.append_assoc, Nat.add_assoc] using h

theorem negateSteps_le (c : ℕ) : negateSteps c ≤ 4 * c + 10 := by
  unfold negateSteps
  omega

theorem negate_runsIn_inputLength (c : ℕ) (rest output : List Bool) (v p : Bool) :
    RunsIn negateProgram (4 * (Encoding.encodeNat c ++ rest).length + 6)
      (cfg (some 0) v p (Encoding.encodeNat c ++ rest) output)
      (cfg none false false rest
        (Encoding.encodeNat (SubexpFrontend.negateCode c) ++ output)) := by
  refine ⟨_, ?_, negate_trace c rest output v p⟩
  have h := negateSteps_le c
  simp only [List.length_append, Encoding.length_encodeNat]
  omega

theorem negate_literal_trace {n : ℕ} (l : SAT.Literal (Fin n))
    (rest output : List Bool) (v p : Bool) :
    Trace negateProgram (negateSteps (Encoding.literalCode l))
      (cfg (some 0) v p (Encoding.encodeNat (Encoding.literalCode l) ++ rest) output)
      (cfg none false false rest
        (Encoding.encodeNat (Encoding.literalCode l.negate) ++ output)) := by
  rw [SubexpFrontend.literalCode_negate]
  exact negate_trace _ rest output v p

/-- A whole-program theorem starts with the actual raw input word. -/
theorem negate_complete_trace (c : ℕ) :
    Trace negateProgram (negateSteps c)
      (initial negateProgram (Encoding.encodeNat c))
      (terminal negateProgram (Encoding.encodeNat (SubexpFrontend.negateCode c))) := by
  have hi : initial negateProgram (Encoding.encodeNat c) =
      cfg (some 0) false false (Encoding.encodeNat c) [] := by
    simp [initial, cfg ]
    constructor <;> funext i <;> fin_cases i <;> rfl
  have ht : terminal negateProgram (Encoding.encodeNat (SubexpFrontend.negateCode c)) =
      cfg none false false [] (Encoding.encodeNat (SubexpFrontend.negateCode c)) := by
    simp [terminal, cfg ]
    constructor <;> funext i <;> fin_cases i <;> rfl
  rw [hi, ht]
  simpa using negate_trace c [] [] false false

theorem negate_primitive_execution (c : ℕ) :
    Computation.RunsIn (primitive negateProgram).step
      (primitiveOverhead negateProgram * negateSteps c)
      ((primitive negateProgram).init (Encoding.encodeNat c))
      (primitiveCfg negateProgram
        (terminal negateProgram (Encoding.encodeNat (SubexpFrontend.negateCode c)))) := by
  simpa only [primitive_initial] using
    primitive_trace negateProgram (negate_complete_trace c)

/-- The complement query generated by the program is exactly the opposite
literal's membership query in the executable list representation. -/
theorem contains_negate_literalCode {n : ℕ} (l : SAT.Literal (Fin n))
    (C : SAT.Clause (Fin n)) :
    ExecCNF.contains (SubexpFrontend.negateCode (Encoding.literalCode l))
      (Encoding.clauseNumbers C) = true ↔ l.negate ∈ C := by
  rw [ExecCNF.contains_true, ← SubexpFrontend.literalCode_negate]
  simp only [Encoding.clauseNumbers, Finset.mem_sort, Finset.mem_image]
  constructor
  · rintro ⟨l', hl', heq⟩
    exact Encoding.literalCode_injective heq ▸ hl'
  · intro h
    exact ⟨l.negate, h, rfl⟩

/-- This identifies the list predicate that the eventual tautology filter must
compute; it does not assume that the filter has been compiled. -/
theorem tautology_clauseNumbers {n : ℕ} (C : SAT.Clause (Fin n)) :
    ExecCNF.tautology SubexpFrontend.negateCode (Encoding.clauseNumbers C) = true ↔
      C.IsTautology := by
  simp only [ExecCNF.tautology, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hneg⟩
    have hc' : c ∈ C.image Encoding.literalCode := by
      simpa [Encoding.clauseNumbers] using hc
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hc'
    exact ⟨l, hl, (contains_negate_literalCode l C).mp hneg⟩
  · rintro ⟨l, hl, hneg⟩
    refine ⟨Encoding.literalCode l, ?_, (contains_negate_literalCode l C).mpr hneg⟩
    simpa [Encoding.clauseNumbers] using Finset.mem_image.mpr ⟨l, hl, rfl⟩

/-! ## Actual record-filter output step

The predicate's result occupies register 2. The following fixed callback
consumes the reversed record on stack 3, prepends its framed representation to
stack 2 exactly when selected, and resets the iterator's flags. Its two other
stacks are preserved. Computing the selection bit is a separate operation.
-/

def filterState (value present selected : Bool)
    (source work output payload : List Bool) : StructuredProgram.State 3 4 :=
  ⟨SubexpPostfixControl.triple value present selected,
    SubexpPostfixControl.quadruple source work output payload⟩

/-- Enter the proved frame writer directly at its fixed encoding entry. -/
abbrev emitRecordProgram : Program 3 4 17 :=
  { SubexpPostfixControl.literalService with inputStack := 3, entry := 7 }

theorem emitRecord_trace (bits source work output : List Bool) (v p selected : Bool) :
    Trace emitRecordProgram (5 * bits.length + 7)
      ((filterState v p selected source work output bits.reverse).withPC
        (some emitRecordProgram.entry))
      ((filterState true false selected source work
        (true :: (Encoding.frame bits ++ output)) []).withPC none) := by
  have hstep : step emitRecordProgram = step SubexpPostfixControl.literalService := by
    funext c
    rfl
  change SubexponentialSAT.Computation.Trace (step emitRecordProgram) _ _ _
  rw [hstep]
  simpa only [emitRecordProgram, step, filterState, StructuredProgram.State.withPC,
    SubexpPostfixControl.cfg4] using
      SubexpPostfixControl.literalService_encode_trace bits source work output v p selected

abbrev discardRecordProgram : Program 3 4 3 := StackRoutines.clearProgram 3 0 1

theorem discardRecord_trace (bits source work output : List Bool) (v p selected : Bool) :
    Trace discardRecordProgram (2 * bits.length + 3)
      ((filterState v p selected source work output bits.reverse).withPC
        (some discardRecordProgram.entry))
      ((filterState false false selected source work output []).withPC none) := by
  have h := StackRoutines.clearProgram_trace (r := 3) (s := 4) 3 0 1
    (SubexpPostfixControl.triple v p selected)
    (SubexpPostfixControl.quadruple source work output bits.reverse)
  have hh := StackRoutines.halt_after_trace (StackRoutines.clearProgram (3 : Fin 4)
    (0 : Fin 3) 1) h 2 rfl rfl
  simpa [discardRecordProgram, StackRoutines.clearProgram, StackRoutines.clearResult,
    StackRoutines.clearStacks, filterState, StructuredProgram.State.withPC,
    readRegs, Nat.add_assoc] using hh

abbrev resetFilterFlags : StructuredProgram.Cmd 3 4 :=
  .seq (.atom (.set 0 false)) (.seq (.atom (.set 1 true)) (.atom (.set 2 false)))

theorem resetFilterFlags_eval (v p selected : Bool)
    (source work output payload : List Bool) :
    StructuredProgram.Eval resetFilterFlags 3
      (filterState v p selected source work output payload)
      (filterState false true false source work output payload) := by
  have h0 : StructuredProgram.Eval (.atom (.set 0 false)) 1
      (filterState v p selected source work output payload)
      (filterState false p selected source work output payload) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 0 false)
        (filterState v p selected source work output payload)
  have h1 : StructuredProgram.Eval (.atom (.set 1 true)) 1
      (filterState false p selected source work output payload)
      (filterState false true selected source work output payload) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 1 true)
        (filterState false p selected source work output payload)
  have h2 : StructuredProgram.Eval (.atom (.set 2 false)) 1
      (filterState false true selected source work output payload)
      (filterState false true false source work output payload) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 2 false)
        (filterState false true selected source work output payload)
  exact .seq h0 (.seq h1 h2)

abbrev emitIfSelected : StructuredCalls.Cmd 3 4 :=
  .seq (.ite 2 (.call emitRecordProgram) (.call discardRecordProgram))
    (.base resetFilterFlags)

def emitIfSelectedSteps (selected : Bool) (bits : List Bool) : ℕ :=
  if selected then 5 * bits.length + 11 else 2 * bits.length + 7

/-- An actual measured branch: the kept record is encoded, and an omitted
record is consumed. Both paths leave the callback ready for the next record. -/
theorem emitIfSelected_eval (selected : Bool)
    (bits source work output : List Bool) (v p : Bool) :
    StructuredCalls.Eval emitIfSelected (emitIfSelectedSteps selected bits)
      (filterState v p selected source work output bits.reverse)
      (filterState false true false source work
        (if selected then true :: (Encoding.frame bits ++ output) else output) []) := by
  cases selected with
  | false =>
      have hc := StructuredCalls.Eval.call discardRecordProgram
        (discardRecord_trace bits source work output v p false)
      have hi := StructuredCalls.Eval.ite_false (yes := .call emitRecordProgram)
        (test := (2 : Fin 3)) (by rfl) hc
      have hs := hi.seq (StructuredCalls.Eval.base
        (resetFilterFlags_eval false false false source work output []))
      simpa [emitIfSelected, emitIfSelectedSteps, Nat.add_assoc] using hs
  | true =>
      have hc := StructuredCalls.Eval.call emitRecordProgram
        (emitRecord_trace bits source work output v p true)
      have hi := StructuredCalls.Eval.ite_true (no := .call discardRecordProgram)
        (test := (2 : Fin 3)) (by rfl) hc
      have hs := hi.seq (StructuredCalls.Eval.base
        (resetFilterFlags_eval true false true source work
          (true :: (Encoding.frame bits ++ output)) []))
      simpa [emitIfSelected, emitIfSelectedSteps, Nat.add_assoc] using hs

def emitIfSelectedProgram := StructuredCalls.compiled emitIfSelected 3 2

theorem emitIfSelected_trace (selected : Bool)
    (bits source work output : List Bool) (v p : Bool) :
    Trace emitIfSelectedProgram (emitIfSelectedSteps selected bits + 1)
      ((filterState v p selected source work output bits.reverse).withPC
        (some emitIfSelectedProgram.entry))
      ((filterState false true false source work
        (if selected then true :: (Encoding.frame bits ++ output) else output) []).withPC none) :=
  StructuredCalls.compiled_halt_trace
    (emitIfSelected_eval selected bits source work output v p) 3 2

theorem emitIfSelected_steps_le (selected : Bool) (bits : List Bool) :
    emitIfSelectedSteps selected bits + 1 ≤ 5 * bits.length + 12 := by
  unfold emitIfSelectedSteps
  split <;> omega

theorem emitIfSelected_primitive_execution (selected : Bool)
    (bits source work output : List Bool) (v p : Bool) :
    Computation.RunsIn (primitive emitIfSelectedProgram).step
      (primitiveOverhead emitIfSelectedProgram * (emitIfSelectedSteps selected bits + 1))
      (primitiveCfg emitIfSelectedProgram
        ((filterState v p selected source work output bits.reverse).withPC
          (some emitIfSelectedProgram.entry)))
      (primitiveCfg emitIfSelectedProgram
        ((filterState false true false source work
          (if selected then true :: (Encoding.frame bits ++ output) else output) []).withPC none)) :=
  primitive_trace emitIfSelectedProgram
    (emitIfSelected_trace selected bits source work output v p)

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

def filterPorts : RecordPrograms.Ports 3 4 where
  tag := 0
  present := 1
  found := 2
  source := 0
  payload := 3
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem recordState_eq (base : StructuredProgram.State 3 4)
    (v p f : Bool) (source payload : List Bool) :
    RecordPrograms.state filterPorts base v p f source payload =
      filterState v p f source (base.stacks 1) (base.stacks 2) payload := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [ filterPorts,
      SubexpPostfixControl.triple]
  · funext i
    fin_cases i <;> simp [ filterPorts,
      SubexpPostfixControl.quadruple]

abbrev emitEveryRecord : StructuredCalls.Cmd 3 4 :=
  .seq (.base (.atom (.set 2 true))) emitIfSelected

theorem emitEveryRecord_eval (bits source work output : List Bool) (v p f : Bool) :
    StructuredCalls.Eval emitEveryRecord (5 * bits.length + 12)
      (filterState v p f source work output bits.reverse)
      (filterState false true false source work
        (true :: (Encoding.frame bits ++ output)) []) := by
  have hset : StructuredProgram.Eval (.atom (.set 2 true)) 1
      (filterState v p f source work output bits.reverse)
      (filterState v p true source work output bits.reverse) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 2 true)
        (filterState v p f source work output bits.reverse)
  have h := (StructuredCalls.Eval.base hset).seq
    (emitIfSelected_eval true bits source work output v p)
  have ht : 1 + emitIfSelectedSteps true bits = 5 * bits.length + 12 := by
    simp only [emitIfSelectedSteps, ite_true]
    omega
  simpa only [ht, emitEveryRecord, Bool.true_eq, ite_true] using h

def PrependEffect (bits : List Bool)
    (before after : StructuredProgram.State 3 4) : Prop :=
  after.stacks 1 = before.stacks 1 ∧
    after.stacks 2 = true :: (Encoding.frame bits ++ before.stacks 2)

theorem emitEveryRecord_contract :
    RecordPrograms.CallbackContractWith filterPorts emitEveryRecord
      (fun _ => false) (fun bits => 5 * bits.length + 12) (fun _ => True) PrependEffect := by
  intro bits tail base _
  let next : StructuredProgram.State 3 4 :=
    { base with «stacks» :=
        Function.update base.stacks 2 (true :: (Encoding.frame bits ++ base.stacks 2)) }
  refine ⟨5 * bits.length + 12, next, le_rfl, trivial, ?_, ?_⟩
  · simp [PrependEffect, next]
  · rw [recordState_eq, recordState_eq]
    simpa [next] using
      emitEveryRecord_eval bits tail (base.stacks 1) (base.stacks 2) false true false

theorem prependVisits_result {records : List (List Bool)}
    {before after : StructuredProgram.State 3 4}
    (h : RecordPrograms.Visits (fun _ => false) PrependEffect records before after)
    (acc : List (List Bool)) (hacc : before.stacks 2 = Encoding.encodeList id acc) :
    after.stacks 2 = Encoding.encodeList id (records.reverse ++ acc) ∧
      after.stacks 1 = before.stacks 1 := by
  induction h generalizing acc with
  | nil base => simpa using And.intro hacc (Eq.refl (base.stacks 1))
  | hit ht _ => cases ht
  | @miss bits records before middle after _ he _ ih =>
      have hm : middle.stacks 2 = Encoding.encodeList id (bits :: acc) := by
        rw [he.2, hacc]
        rfl
      obtain ⟨hout, hwork⟩ := ih (bits :: acc) hm
      refine ⟨?_, hwork.trans he.1⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hout

@[simp] theorem unread_false (records : List (List Bool)) (suffix : List Bool) :
    RecordPrograms.unread (fun _ => false) records suffix = suffix := by
  induction records with
  | nil => rfl
  | cons bits records ih => simpa [RecordPrograms.unread] using ih

abbrev reverseRecordsCmd : StructuredCalls.Cmd 3 4 :=
  RecordPrograms.iterate filterPorts emitEveryRecord

theorem reverseRecords_eval (records acc : List (List Bool))
    (suffix work : List Bool) (v p f : Bool) :
    ∃ n, n ≤ 3 + RecordPrograms.budget (fun bits => 5 * bits.length + 12) records ∧
      StructuredCalls.Eval reverseRecordsCmd n
        (filterState v p f (Encoding.encodeList id records ++ suffix) work
          (Encoding.encodeList id acc) [])
        (filterState false true false suffix work
          (Encoding.encodeList id (records.reverse ++ acc)) []) := by
  let base := filterState false true false [] work (Encoding.encodeList id acc) []
  obtain ⟨n, next, hn, _, hhistory, hrun⟩ :=
    RecordPrograms.iterate_run_with filterPorts emitEveryRecord
      (fun _ => false) (fun bits => 5 * bits.length + 12) (fun _ => True) PrependEffect
      emitEveryRecord_contract records suffix base trivial v p f
  obtain ⟨hout, hwork⟩ := prependVisits_result hhistory acc rfl
  rw [recordState_eq, recordState_eq, hout, hwork] at hrun
  have hany : records.any (fun _ => false) = false := by
    induction records <;> simp_all
  refine ⟨n, hn, ?_⟩
  simpa [reverseRecordsCmd, base, filterState, hany] using hrun

theorem reverseRecords_budget (records : List (List Bool)) :
    RecordPrograms.budget (fun bits => 5 * bits.length + 12) records =
      11 * (records.map List.length).sum + 19 * records.length := by
  induction records with
  | nil => rfl
  | cons bits records ih =>
      simp only [RecordPrograms.budget, ih, List.map_cons, List.sum_cons, List.length_cons]
      omega

def reverseRecordsProgram := StructuredCalls.compiled reverseRecordsCmd 0 2

/-- The entire record reversal pass takes linearly many actual instructions.
It preserves a trailing input suffix and the separate work stack. -/
theorem reverseRecords_runsIn (records acc : List (List Bool))
    (suffix work : List Bool) (v p f : Bool) :
    RunsIn reverseRecordsProgram (10 * (Encoding.encodeList id records).length)
      ((filterState v p f (Encoding.encodeList id records ++ suffix) work
        (Encoding.encodeList id acc) []).withPC (some reverseRecordsProgram.entry))
      ((filterState false true false suffix work
        (Encoding.encodeList id (records.reverse ++ acc)) []).withPC none) := by
  obtain ⟨n, hn, hrun⟩ := reverseRecords_eval records acc suffix work v p f
  refine ⟨n + 1, ?_, StructuredCalls.compiled_halt_trace hrun 0 2⟩
  rw [reverseRecords_budget] at hn
  have hlength := ProgramEncoding.encodeRecords_length records
  change (Encoding.encodeList id records).length = _ at hlength
  omega

/-! ## Exact-order contract for the full normalization filter

The selection callback in the following theorem is a fixed structured
program with measured executions. No procedure is manufactured from the
mathematical predicate. Once that callback is supplied, the theorem tracks
the output of the actual generic record iterator, including record order.
-/

def FilterEffect {r s : ℕ} (output : Fin s) (keep : List Bool → Bool)
    (bits : List Bool) (before after : StructuredProgram.State r s) : Prop :=
  after.stacks output =
    if keep bits then true :: (Encoding.frame bits ++ before.stacks output)
    else before.stacks output

theorem filterVisits_result {r s : ℕ} (output : Fin s) (keep : List Bool → Bool)
    {records : List (List Bool)} {before after : StructuredProgram.State r s}
    (h : RecordPrograms.Visits (fun _ => false) (FilterEffect output keep)
      records before after)
    (acc : List (List Bool)) (hacc : before.stacks output = Encoding.encodeList id acc) :
    after.stacks output = Encoding.encodeList id ((records.filter keep).reverse ++ acc) := by
  induction h generalizing acc with
  | nil base => simpa using hacc
  | hit ht _ => cases ht
  | @miss bits records before middle after _ he _ ih =>
      cases hkeep : keep bits with
      | false =>
          have hm : middle.stacks output = Encoding.encodeList id acc := by
            simpa [FilterEffect, hkeep, hacc] using he
          simpa [List.filter_cons, hkeep] using ih acc hm
      | true =>
          have hm : middle.stacks output = Encoding.encodeList id (bits :: acc) := by
            simpa [FilterEffect, hkeep, hacc, Encoding.encodeList] using he
          simpa [List.filter_cons, hkeep, List.reverse_cons, List.append_assoc] using
            ih (bits :: acc) hm

/-- A correctness interface for normalization's actual filter callback. The
conclusion tracks `reverse (List.filter keep records)` exactly. Applying
`reverseRecordsProgram` afterward restores `List.filter` order. -/
theorem filter_iterate_run {r s : ℕ} (ports : RecordPrograms.Ports r s)
    (callback : StructuredCalls.Cmd r s) (keep : List Bool → Bool)
    (cost : List Bool → ℕ) (invariant : StructuredProgram.State r s → Prop)
    (output : Fin s)
    (hsource : output ≠ ports.source) (hpayload : output ≠ ports.payload)
    (contract : RecordPrograms.CallbackContractWith ports callback
      (fun _ => false) cost invariant (FilterEffect output keep))
    (records acc : List (List Bool)) (suffix : List Bool)
    (base : StructuredProgram.State r s) (hbase : invariant base)
    (hacc : base.stacks output = Encoding.encodeList id acc) (v p f : Bool) :
    ∃ (n : ℕ) (next : StructuredProgram.State r s),
      n ≤ 3 + RecordPrograms.budget cost records ∧ invariant next ∧
      (RecordPrograms.state ports next false true false suffix []).stacks output =
        Encoding.encodeList id ((records.filter keep).reverse ++ acc) ∧
      StructuredCalls.Eval (RecordPrograms.iterate ports callback) n
        (RecordPrograms.state ports base v p f (Encoding.encodeList id records ++ suffix) [])
        (RecordPrograms.state ports next false true false suffix []) := by
  obtain ⟨n, next, hn, hnext, hhistory, hrun⟩ :=
    RecordPrograms.iterate_run_with ports callback (fun _ => false) cost invariant
      (FilterEffect output keep) contract records suffix base hbase v p f
  have hout := filterVisits_result output keep hhistory acc hacc
  have hany : records.any (fun _ => false) = false := by
    induction records <;> simp_all
  have hfinal := (RecordPrograms.state_stack_frame ports next false true false
    suffix [] output hsource hpayload).trans hout
  exact ⟨n, next, hn, hnext, hfinal, by simpa [hany] using hrun⟩

end SubexponentialSAT.SubexpNormalizeProgram

end OAI.Algorithms
