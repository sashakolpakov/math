import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# Fixed-control extraction-job phase

An extraction job contains three framed words: the unary output position,
the fixed-width coefficient key, and the serialized postfix moment program.
Repeating a moment program for each U,Z coefficient adds only the polynomial
factor D(D+1). This permits one flat input loop and one fixed coefficient
lookup/update body.

The concrete control below links finite instruction tables. The three service
tables are the postfix interpreter, the coefficient-list scanner, and quartic
addition. Their complete input/output trace proofs are integration obligations;
the program does not treat arithmetic as a new atomic instruction.
-/

namespace SubexponentialSAT.SubexpMomentProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 16 128
abbrev Code := StructuredCalls.Cmd 16 128

structure Routine (r s : ℕ) where
  labels : ℕ
  program : BitProgram.Program r s labels

/-- These are actual fixed Boolean instruction tables, not semantic functions.
The evaluator uses stacks 26(code),27(operands),28(depth),29(scratch), returns
the unframed dense result on 15 and clears 27/28. Scanner and addition use the
shared first twenty stacks, including modulus on 5. Caller state is on 100+. -/
structure Services where
  evaluate : Routine 16 128
  lookup : Routine 8 20
  add : Routine 8 20

structure Job where
  outputIndex : List Bool
  coefficientKey : List Bool
  sourceCode : List Bool

def Job.encode (j : Job) : List Bool :=
  Encoding.frame j.outputIndex ++ Encoding.frame j.coefficientKey ++ Encoding.frame j.sourceCode

def input (jobs : List Job) : List Bool := Encoding.encodeList Job.encode jobs

/-- A data-level decoder for the same three frames read by the fixed program.
This is used to state typed record invariants; its execution is not substituted
for the actual parser trace below. -/
def decodeJob (bits : List Bool) : Option Job := do
  let (index, rest) ← Encoding.readFrame bits
  let (key, rest) ← Encoding.readFrame rest
  let (source, rest) ← Encoding.readFrame rest
  if rest = [] then return ⟨index, key, source⟩ else none

@[simp] theorem decodeJob_encode (j : Job) : decodeJob j.encode = some j := by
  have hf (bits : List Bool) : Encoding.readFrame (Encoding.frame bits) = some (bits, []) := by
    simpa only [List.append_nil] using Encoding.readFrame_frame_append bits []
  cases j
  simp [decodeJob, Job.encode, List.append_assoc, hf]

theorem Job.encode_injective : Function.Injective Job.encode := by
  intro j k h
  have hd := congrArg decodeJob h
  exact Option.some.inj (by simpa only [decodeJob_encode] using hd)

theorem input_injective : Function.Injective input :=
  Encoding.encodeList_injective Job.encode_injective

def parserPorts (destination : Fin 128) (h : (101 : Fin 128) ≠ destination) :
    RecordPrograms.Ports 16 128 where
  tag := 0
  present := 1
  found := 15
  source := 101
  payload := destination
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := h

def indexPorts := parserPorts 103 (by decide)
def keyPorts := parserPorts 105 (by decide)
def codePorts := parserPorts 26 (by decide)

def outerPorts : RecordPrograms.Ports 16 128 where
  tag := 13
  present := 14
  found := 15
  source := 100
  payload := 101
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def clear (src : Fin 128) : Code :=
  .call (StackRoutines.clearProgram src 0 1)

def reverse (src : Fin 128) : Code :=
  .call (StackRoutines.reverseProgram src 110 111 0 1)

def moveForward (src dst : Fin 128) : Code :=
  .seq (.call (StackRoutines.transferProgram src 118 0 1))
    (.call (StackRoutines.transferProgram 118 dst 0 1))

def copyIndex : Code := .call (StackRoutines.copyProgram 103 113 114 0 1)

def arrayPorts : Fin 8 → Fin 128 := ![102, 112, 113, 104, 114, 115, 116, 117]

def arrayRead : Code := .call (ProgramLinking.liftProgram
  (ArrayUpdatePrograms.readProgram (0 : Fin 16) 1) id arrayPorts)

def arrayReplace : Code := .call (ProgramLinking.liftProgram
  (ArrayUpdatePrograms.replaceProgram (0 : Fin 16) 1) id arrayPorts)

def scalarCall (p : Routine 8 20) : Code := .call
  (ProgramLinking.liftProgram p.program (Fin.castAdd 8) (Fin.castAdd 108))

def sequence : List Code → Code
  | [] => .base .skip
  | c :: cs => .seq c (sequence cs)

def parseJob : Code := .seq (RecordPrograms.reader indexPorts)
  (.seq (RecordPrograms.reader keyPorts) (RecordPrograms.reader codePorts))

def prepareJob : Code := .seq (reverse 101) (.seq parseJob (reverse 26))

/-- The complete concrete body, including all parsing, data movement, array
read/write and cleanup instructions. The evaluated dense result is unframed
before entering the actual coefficient scanner. -/
def jobBody (svc : Services) : Code := sequence [
  prepareJob,
  .call svc.evaluate.program,
  moveForward 105 14,
  scalarCall svc.lookup,
  copyIndex,
  arrayRead,
  moveForward 112 9,
  scalarCall svc.add,
  moveForward 8 112,
  copyIndex,
  arrayReplace,
  clear 112,
  clear 103,
  clear 14,
  .base (.atom (.set 13 false)),
  .base (.atom (.set 14 true)),
  .base (.atom (.set 15 false))]

def phase (svc : Services) : Code := RecordPrograms.iterate outerPorts (jobBody svc)

/-- This is one finite instruction table for every input size. Its table
depends only on the fixed linked services, never on a job, D, p, or n. -/
def program (svc : Services) : BitProgram.Program 16 128 (StructuredCalls.size (phase svc) + 1) :=
  StructuredCalls.compiled (phase svc) 100 102

def afterFrame (p : RecordPrograms.Ports 16 128) (base : Data)
    (bits tail : List Bool) : Data :=
  RecordPrograms.state p base false true (base.regs p.found)
    tail (bits.reverse ++ base.stacks p.payload)

theorem readFrame_eval (p : RecordPrograms.Ports 16 128) (base : Data)
    (bits tail : List Bool) (hs : base.stacks p.source = Encoding.frame bits ++ tail) :
    StructuredCalls.Eval (RecordPrograms.reader p) (6 * bits.length + 4)
      base (afterFrame p base bits tail) := by
  have h := RecordPrograms.reader_eval p base bits tail (base.stacks p.payload)
    (base.regs p.tag) (base.regs p.present) (base.regs p.found)
  have hi : RecordPrograms.state p base (base.regs p.tag) (base.regs p.present)
      (base.regs p.found) (Encoding.frame bits ++ tail) (base.stacks p.payload) = base :=
    RecordPrograms.state_eq_self p base _ _ _ _ _ rfl rfl rfl hs rfl
  rw [hi] at h
  exact h

def parsedState (base : Data) (j : Job) : Data :=
  let first := afterFrame indexPorts base j.outputIndex
    (Encoding.frame j.coefficientKey ++ Encoding.frame j.sourceCode)
  let second := afterFrame keyPorts first j.coefficientKey (Encoding.frame j.sourceCode)
  afterFrame codePorts second j.sourceCode []

/-- The three job fields are parsed by the actual framed-word programs.
Each output field is reversed, matching the scanner's key ABI and the explicit
source reversal in jobBody. -/
theorem parseJob_eval (base : Data) (j : Job) (hs : base.stacks 101 = j.encode) :
    StructuredCalls.Eval parseJob
      (6 * (j.outputIndex.length + j.coefficientKey.length + j.sourceCode.length) + 12)
      base (parsedState base j) := by
  let first := afterFrame indexPorts base j.outputIndex
    (Encoding.frame j.coefficientKey ++ Encoding.frame j.sourceCode)
  let second := afterFrame keyPorts first j.coefficientKey (Encoding.frame j.sourceCode)
  have h₁ := readFrame_eval indexPorts base j.outputIndex
    (Encoding.frame j.coefficientKey ++ Encoding.frame j.sourceCode)
    (by
      change base.stacks 101 = _
      simpa [Job.encode, List.append_assoc] using hs)
  have h₂ := readFrame_eval keyPorts first j.coefficientKey (Encoding.frame j.sourceCode)
    (by simp [first, afterFrame, indexPorts, keyPorts, parserPorts, RecordPrograms.state])
  have h₃ := readFrame_eval codePorts second j.sourceCode []
    (by simp [second, afterFrame, keyPorts, codePorts, parserPorts, RecordPrograms.state])
  have h := StructuredCalls.Eval.seq h₁ (StructuredCalls.Eval.seq h₂ h₃)
  change StructuredCalls.Eval parseJob _ base (parsedState base j) at h
  convert h using 1
  ring

theorem parsedState_fields (base : Data) (j : Job)
    (hi : base.stacks 103 = []) (hk : base.stacks 105 = []) (hc : base.stacks 26 = []) :
    (parsedState base j).stacks 101 = [] ∧
      (parsedState base j).stacks 103 = j.outputIndex.reverse ∧
      (parsedState base j).stacks 105 = j.coefficientKey.reverse ∧
      (parsedState base j).stacks 26 = j.sourceCode.reverse := by
  simp [parsedState, afterFrame, indexPorts, keyPorts, codePorts, parserPorts,
    RecordPrograms.state, hi, hk, hc]

def reversedState (src : Fin 128) (base : Data) : Data :=
  ⟨BitProgram.readRegs base.regs 0 1 none, StackRoutines.reverseStacks src base.stacks⟩

theorem reverse_eval (src : Fin 128) (h₁ : src ≠ 110) (h₂ : src ≠ 111)
    (base : Data) (ht₁ : base.stacks 110 = []) (ht₂ : base.stacks 111 = []) :
    StructuredCalls.Eval (reverse src) (9 * (base.stacks src).length + 7)
      base (reversedState src base) := by
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.reverseProgram_trace src 110 111 0 1 h₁ h₂ (by decide) (by decide)
      base.regs base.stacks ht₁ ht₂) 9 rfl rfl
  apply StructuredCalls.Eval.call
  simpa [reverse, reversedState, StackRoutines.reverseResult,
    StackRoutines.reverseProgram, StructuredProgram.State.withPC, Nat.add_assoc] using h

def preparedState (base : Data) (j : Job) : Data :=
  reversedState 26 (parsedState (reversedState 101 base) j)

/-- Complete concrete record preparation, including the two reversals needed
by the outer framed-list reader and the postfix evaluator. -/
theorem prepareJob_eval (base : Data) (j : Job)
    (hs : base.stacks 101 = j.encode.reverse)
    (hi : base.stacks 103 = []) (hk : base.stacks 105 = []) (hc : base.stacks 26 = [])
    (ht₁ : base.stacks 110 = []) (ht₂ : base.stacks 111 = []) :
    StructuredCalls.Eval prepareJob
      (9 * j.encode.length + 6 * (j.outputIndex.length + j.coefficientKey.length +
        j.sourceCode.length) + 9 * j.sourceCode.length + 26)
      base (preparedState base j) := by
  have hrev := reverse_eval 101 (by decide) (by decide) base ht₁ ht₂
  have hsrc : (reversedState 101 base).stacks 101 = j.encode := by
    simp [reversedState, StackRoutines.reverseStacks, hs]
  have hp := parseJob_eval (reversedState 101 base) j hsrc
  have fields := parsedState_fields (reversedState 101 base) j
    (by simpa [reversedState, StackRoutines.reverseStacks] using hi)
    (by simpa [reversedState, StackRoutines.reverseStacks] using hk)
    (by simpa [reversedState, StackRoutines.reverseStacks] using hc)
  have htmp (i : Fin 128) (h₁ : i = 110 ∨ i = 111) :
      (parsedState (reversedState 101 base) j).stacks i = [] := by
    rcases h₁ with rfl | rfl <;>
      simp [parsedState, afterFrame, indexPorts, keyPorts, codePorts, parserPorts,
        RecordPrograms.state, reversedState, StackRoutines.reverseStacks, ht₁, ht₂]
  have hout := reverse_eval 26 (by decide) (by decide)
    (parsedState (reversedState 101 base) j) (htmp _ (Or.inl rfl)) (htmp _ (Or.inr rfl))
  have h := StructuredCalls.Eval.seq hrev (StructuredCalls.Eval.seq hp hout)
  rw [hs, List.length_reverse, fields.2.2.2, List.length_reverse] at h
  change StructuredCalls.Eval prepareJob _ base (preparedState base j) at h
  convert h using 1
  ring

theorem preparedState_fields (base : Data) (j : Job)
    (hi : base.stacks 103 = []) (hk : base.stacks 105 = []) (hc : base.stacks 26 = []) :
    (preparedState base j).stacks 101 = [] ∧
      (preparedState base j).stacks 103 = j.outputIndex.reverse ∧
      (preparedState base j).stacks 105 = j.coefficientKey.reverse ∧
      (preparedState base j).stacks 26 = j.sourceCode := by
  simp [preparedState, reversedState, StackRoutines.reverseStacks, parsedState,
    afterFrame, indexPorts, keyPorts, codePorts, parserPorts, RecordPrograms.state,
    hi, hk, hc]

/-- The job parser does not disturb the remaining job stream, output jet,
runtime widths, or any other caller stack. -/
theorem preparedState_preserves (base : Data) (j : Job) (i : Fin 128)
    (h101 : i ≠ 101) (h103 : i ≠ 103) (h105 : i ≠ 105) (h26 : i ≠ 26) :
    (preparedState base j).stacks i = base.stacks i := by
  simp [preparedState, reversedState, StackRoutines.reverseStacks, parsedState,
    afterFrame, indexPorts, keyPorts, codePorts, parserPorts, RecordPrograms.state,
    h101, h103, h105, h26]

theorem Job.encode_length (j : Job) :
    j.encode.length =
      2 * (j.outputIndex.length + j.coefficientKey.length + j.sourceCode.length) + 3 := by
  simp [Job.encode]
  omega

theorem prepareJob_cost_eq (j : Job) :
    9 * j.encode.length + 6 * (j.outputIndex.length + j.coefficientKey.length +
      j.sourceCode.length) + 9 * j.sourceCode.length + 26 =
      24 * j.outputIndex.length + 24 * j.coefficientKey.length +
        33 * j.sourceCode.length + 53 := by
  rw [Job.encode_length]
  ring

end SubexponentialSAT.SubexpMomentProgram

end OAI.Algorithms
