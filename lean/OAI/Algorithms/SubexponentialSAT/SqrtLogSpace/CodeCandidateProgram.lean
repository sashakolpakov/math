import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators

/-! Fixed-table conversion of one odometer tuple to one arithmetic candidate.
The input contains only the current candidate. The output is reversed scalar
frames, directly suitable for the existing word and matrix callbacks. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram

open BitProgram CodeCandidates

/-- Construct the zero candidate from a runtime unary dimension word.
The instruction table is independent of the dimension. -/
def zeroTupleProgram : Program 4 2 12 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.set 0 false 1, .set 1 true 2, .push 1 0 3,
    .pop 0 2 3 4, .branch 3 5 11,
    .push 1 0 6, .push 1 0 7, .push 1 1 8,
    .push 1 0 9, .push 1 1 10, .push 1 1 3, .halt]

def initializeCfg (pc : Option (Fin 12)) (regs : Fin 4 → Bool)
    (input output : List Bool) : Cfg 4 2 12 := ⟨pc, regs, ![input, output]⟩

private theorem initialize_round (bit : Bool) (input output : List Bool)
    (regs : Fin 4 → Bool) (hzero : regs 0 = false) (hone : regs 1 = true) :
    Trace zeroTupleProgram 8 (initializeCfg (some 3) regs (bit :: input) output)
      (initializeCfg (some 3) (readRegs regs 2 3 (some bit)) input
        (true :: true :: false :: true :: false :: false :: output)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, zeroTupleProgram, initializeCfg, execInstr,
    readRegs, Function.update_apply, hzero, hone]
  funext i
  fin_cases i <;> simp

private theorem initialize_loop (input output : List Bool) (regs : Fin 4 → Bool)
    (hzero : regs 0 = false) (hone : regs 1 = true) :
    ∃ rf, Trace zeroTupleProgram (8 * input.length + 3)
      (initializeCfg (some 3) regs input output)
      (initializeCfg none rf []
        ((List.replicate input.length [true, true, false, true, false, false]).flatten ++ output)) := by
  induction input generalizing regs output with
  | nil =>
      refine ⟨readRegs regs 2 3 none, ?_⟩
      apply Computation.Trace.of_iterate
      simp [Function.iterate_succ_apply, step, zeroTupleProgram, initializeCfg, execInstr,
        readRegs, Function.update_apply]
  | cons bit input ih =>
      obtain ⟨rf, hr⟩ := ih
        (true :: true :: false :: true :: false :: false :: output)
        (readRegs regs 2 3 (some bit))
        (by simpa [readRegs] using hzero) (by simpa [readRegs] using hone)
      refine ⟨rf, ?_⟩
      have h := (initialize_round bit input output regs hzero hone).trans hr
      simpa [List.length_cons, List.replicate_succ', List.flatten_append,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using h

private theorem initialize_encoding (d : ℕ) :
    (List.replicate d [true, true, false, true, false, false]).flatten ++ [false] =
      Encoding.encodeList id (List.replicate d [false, false]) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simpa [List.replicate_succ, Encoding.encodeList, Encoding.frame] using
        congrArg (fun rest => true :: true :: false :: true :: false :: false :: rest) ih

/-- Empty dimensions produce the one-bit empty tuple, not an absent witness. -/
theorem initialize_trace (input : List Bool) (regs : Fin 4 → Bool) :
    ∃ rf, Trace zeroTupleProgram (8 * input.length + 6)
      (initializeCfg (some zeroTupleProgram.entry) regs input [])
      (initializeCfg none rf []
        (Encoding.encodeList id (List.replicate input.length [false, false]))) := by
  let ready := Function.update (Function.update regs 0 false) 1 true
  have hstart : Trace zeroTupleProgram 3 (initializeCfg (some zeroTupleProgram.entry) regs input [])
      (initializeCfg (some 3) ready input [false]) := by
    apply Computation.Trace.of_iterate
    simp [Function.iterate_succ_apply, step, zeroTupleProgram, initializeCfg, execInstr, ready]
    funext i
    fin_cases i <;> rfl
  obtain ⟨rf, hr⟩ := initialize_loop input [false] ready (by simp [ready]) (by simp [ready])
  refine ⟨rf, ?_⟩
  have h := hstart.trans hr
  have htime : 3 + (8 * input.length + 3) = 8 * input.length + 6 := by omega
  rw [htime] at h
  simpa [initialize_encoding] using h

theorem initialize_prefix_space (input : List Bool) (regs : Fin 4 → Bool)
    {prefixSteps : ℕ} {state : Cfg 4 2 12} (hle : prefixSteps ≤ 8 * input.length + 6)
    (trace : Trace zeroTupleProgram prefixSteps
      (initializeCfg (some zeroTupleProgram.entry) regs input []) state) :
    dataBits state ≤ 9 * input.length + 6 := by
  have h := trace_dataBits zeroTupleProgram trace
  have hi : dataBits (initializeCfg (some zeroTupleProgram.entry) regs input []) = input.length := by
    simp [dataBits, stackBits, initializeCfg, Fin.sum_univ_succ]
  rw [hi] at h
  omega

/-- The dimension is consumed from one caller port; all other caller tapes
survive the concrete constructor call. -/
theorem initialize_call {R S : ℕ} (register : Fin 4 ↪ Fin R) (stack : Fin 2 ↪ Fin S)
    (a : StructuredCalls.State R S) (houtput : a.stacks (stack 1) = []) :
    ∃ b : StructuredCalls.State R S,
      StructuredCalls.Eval (.call (ProgramLinking.liftProgram zeroTupleProgram register stack))
        (8 * (a.stacks (stack 0)).length + 6) a b ∧
      b.stacks (stack 0) = [] ∧
      b.stacks (stack 1) = Encoding.encodeList id
        (List.replicate (a.stacks (stack 0)).length [false, false]) ∧
      (∀ i, (¬ ∃ j, stack j = i) → b.stacks i = a.stacks i) ∧
      (∀ i, (¬ ∃ j, register j = i) → b.regs i = a.regs i) := by
  obtain ⟨rf, ht⟩ := initialize_trace (a.stacks (stack 0)) (a.regs ∘ register)
  let final : StructuredCalls.State 4 2 :=
    ⟨rf, ![[], Encoding.encodeList id
      (List.replicate (a.stacks (stack 0)).length [false, false])]⟩
  have hstart : (StructuredCalls.projectState register stack a).withPC
      (some zeroTupleProgram.entry) =
      initializeCfg (some zeroTupleProgram.entry) (a.regs ∘ register)
        (a.stacks (stack 0)) [] := by
    change (⟨some zeroTupleProgram.entry, a.regs ∘ register, a.stacks ∘ stack⟩ : Cfg 4 2 12) = _
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact houtput
  have ht' : Trace zeroTupleProgram (8 * (a.stacks (stack 0)).length + 6)
      ((StructuredCalls.projectState register stack a).withPC (some zeroTupleProgram.entry))
      (final.withPC none) := by rw [hstart]; exact ht
  refine ⟨StructuredCalls.embedState register stack a final,
    StructuredCalls.eval_call_from_state zeroTupleProgram register stack a
      register.injective stack.injective ht', ?_, ?_, ?_, ?_⟩
  · exact StructuredCalls.embedState_stack _ _ _ _ stack.injective 0
  · exact StructuredCalls.embedState_stack _ _ _ _ stack.injective 1
  · exact fun i hi => StructuredCalls.embedState_stack_frame _ _ _ _ i hi
  · exact fun i hi => StructuredCalls.embedState_register_frame _ _ _ _ i hi

/-- `ternary = false` is the graph alphabet; `true` is the local-code alphabet.
Register 4 reports an unused digit. No candidate family is ever constructed. -/
def convert (ternary : Bool) : Program 5 2 18 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.set 4 false 1, .pop 0 0 1 2, .branch 0 3 17,
    .pop 0 0 1 4, .pop 0 2 1 5, .pop 0 0 1 6, .pop 0 3 1 7,
    .pop 0 0 1 8, .set 0 true 9, .push 1 0 10, .push 1 2 11,
    .push 1 0 12, .push 1 3 13, .set 0 false 14, .push 1 0 15,
    (if ternary then .band 2 2 3 16 else .copy 2 3 16),
    .bor 4 4 2 1, .halt]

def cfg (pc : Option (Fin 18)) (regs : Fin 5 → Bool)
    (input output : List Bool) : Cfg 5 2 18 :=
  ⟨pc, regs, ![input, output]⟩

private def roundRegs (ternary : Bool) (regs : Fin 5 → Bool) (a b : Bool) : Fin 5 → Bool :=
  ![false, true, invalidDigit ternary (a,b), b, regs 4 || invalidDigit ternary (a,b)]

private theorem convert_read (ternary a b : Bool) (regs : Fin 5 → Bool)
    (input output : List Bool) :
    Trace (convert ternary) 7
      (cfg (some 1) regs (true :: true :: a :: true :: b :: false :: input) output)
      (cfg (some 8) ![false, true, a, b, regs 4] input output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, convert, cfg, execInstr, readRegs,
    Function.update_apply]
  constructor <;> funext i <;> fin_cases i <;> simp

private theorem convert_write (ternary a b : Bool) (regs : Fin 5 → Bool)
    (input output : List Bool) :
    Trace (convert ternary) 9
      (cfg (some 8) ![false, true, a, b, regs 4] input output)
      (cfg (some 1) (roundRegs ternary regs a b) input
        (false :: b :: true :: a :: true :: output)) := by
  cases ternary <;>
    apply Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, convert, cfg, roundRegs, invalidDigit,
      execInstr, readRegs, Function.update_apply] <;>
    constructor <;> funext i <;> fin_cases i <;> simp

private theorem convert_round (ternary a b : Bool) (regs : Fin 5 → Bool)
    (input output : List Bool) :
    Trace (convert ternary) 16
      (cfg (some 1) regs (true :: true :: a :: true :: b :: false :: input) output)
      (cfg (some 1) (roundRegs ternary regs a b) input
        (false :: b :: true :: a :: true :: output)) :=
  (convert_read ternary a b regs input output).trans
    (convert_write ternary a b regs input output)

private theorem convert_exit (ternary : Bool) (regs : Fin 5 → Bool) (output : List Bool) :
    Trace (convert ternary) 3
      (cfg (some 1) regs [false] output)
      (cfg none (readRegs regs 0 1 (some false)) [] output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, convert, cfg, execInstr, readRegs,
    Function.update_apply]
  funext i
  fin_cases i <;> simp

private theorem convert_loop (ternary : Bool) (xs : List (Bool × Bool))
    (regs : Fin 5 → Bool) (output : List Bool) :
    ∃ rf, rf 4 = (regs 4 || xs.any (invalidDigit ternary)) ∧
      Trace (convert ternary) (16 * xs.length + 3)
        (cfg (some 1) regs (tupleBits xs) output)
        (cfg none rf [] ((scalarFrames xs).reverse ++ output)) := by
  induction xs generalizing regs output with
  | nil =>
    refine ⟨readRegs regs 0 1 (some false), ?_, ?_⟩
    · simp [readRegs]
    · simpa [tupleBits, scalarFrames, Encoding.encodeList] using convert_exit ternary regs output
  | cons x xs ih =>
    rcases x with ⟨a,b⟩
    obtain ⟨rf, hr, ht⟩ := ih (roundRegs ternary regs a b)
      (false :: b :: true :: a :: true :: output)
    refine ⟨rf, ?_, ?_⟩
    · simpa [roundRegs, Bool.or_assoc] using hr
    · have h := (convert_round ternary a b regs (tupleBits xs) output).trans ht
      simpa [tupleBits, scalarFrames, Encoding.encodeList, Encoding.frame, digitBits,
        Function.comp_def, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        List.append_assoc] using h

/-- Complete execution, including initialization, every rejected digit and halt. -/
theorem convert_trace (ternary : Bool) (xs : List (Bool × Bool))
    (regs : Fin 5 → Bool) (output : List Bool) :
    ∃ rf, rf 4 = xs.any (invalidDigit ternary) ∧
      Trace (convert ternary) (16 * xs.length + 4)
        (cfg (some 0) regs (tupleBits xs) output)
        (cfg none rf [] ((scalarFrames xs).reverse ++ output)) := by
  obtain ⟨rf, hr, ht⟩ := convert_loop ternary xs (Function.update regs 4 false) output
  refine ⟨rf, by simpa using hr, ?_⟩
  have hstart : step (convert ternary) (cfg (some 0) regs (tupleBits xs) output) =
      some (cfg (some 1) (Function.update regs 4 false) (tupleBits xs) output) := by
    simp [step, convert, cfg, execInstr]
  have h := Computation.Trace.cons hstart ht
  convert h using 1

/-- The bound covers both stacks at every concrete source prefix. This uses
only the linear cost of one candidate conversion, never the search duration. -/
theorem convert_prefix_space (ternary : Bool) (xs : List (Bool × Bool))
    (regs : Fin 5 → Bool) (output : List Bool) {prefixSteps : ℕ} {state : Cfg 5 2 18}
    (hle : prefixSteps ≤ 16 * xs.length + 4)
    (trace : Trace (convert ternary) prefixSteps (cfg (some 0) regs (tupleBits xs) output) state) :
    dataBits state ≤ 22 * xs.length + output.length + 5 := by
  have h := trace_dataBits (convert ternary) trace
  have hi : dataBits (cfg (some 0) regs (tupleBits xs) output) =
      6 * xs.length + 1 + output.length := by
    simp [dataBits, stackBits, cfg, Fin.sum_univ_succ]
  rw [hi] at h
  omega

/-- Concrete port relocation, preserving the entire off-port caller frame. -/
theorem convert_call {R S : ℕ} (ternary : Bool)
    (register : Fin 5 ↪ Fin R) (stack : Fin 2 ↪ Fin S)
    (xs : List (Bool × Bool)) (a : StructuredCalls.State R S)
    (hinput : a.stacks (stack 0) = tupleBits xs) :
    ∃ b : StructuredCalls.State R S,
      StructuredCalls.Eval (.call (ProgramLinking.liftProgram (convert ternary) register stack))
        (16 * xs.length + 4) a b ∧
      b.regs (register 4) = xs.any (invalidDigit ternary) ∧
      b.stacks (stack 0) = [] ∧
      b.stacks (stack 1) = (scalarFrames xs).reverse ++ a.stacks (stack 1) ∧
      (∀ i, (¬ ∃ j, stack j = i) → b.stacks i = a.stacks i) ∧
      (∀ i, (¬ ∃ j, register j = i) → b.regs i = a.regs i) := by
  obtain ⟨rf, hr, ht⟩ := convert_trace ternary xs (a.regs ∘ register) (a.stacks (stack 1))
  let final : StructuredCalls.State 5 2 :=
    ⟨rf, ![[], (scalarFrames xs).reverse ++ a.stacks (stack 1)]⟩
  have hstart : (StructuredCalls.projectState register stack a).withPC (some (convert ternary).entry) =
      cfg (some 0) (a.regs ∘ register) (tupleBits xs) (a.stacks (stack 1)) := by
    change (⟨some 0, a.regs ∘ register, a.stacks ∘ stack⟩ : Cfg 5 2 18) = _
    congr 1
    funext i
    fin_cases i
    · exact hinput
    · rfl
  have ht' : Trace (convert ternary) (16 * xs.length + 4)
      ((StructuredCalls.projectState register stack a).withPC (some (convert ternary).entry))
      (final.withPC none) := by rw [hstart]; exact ht
  refine ⟨StructuredCalls.embedState register stack a final,
    StructuredCalls.eval_call_from_state (convert ternary) register stack a
      register.injective stack.injective ht', ?_, ?_, ?_, ?_, ?_⟩
  · exact (StructuredCalls.embedState_register _ _ _ _ register.injective 4).trans hr
  · exact StructuredCalls.embedState_stack _ _ _ _ stack.injective 0
  · exact StructuredCalls.embedState_stack _ _ _ _ stack.injective 1
  · exact fun i hi => StructuredCalls.embedState_stack_frame _ _ _ _ i hi
  · exact fun i hi => StructuredCalls.embedState_register_frame _ _ _ _ i hi

/-- Retain the first successful current candidate. The callback is actual
fixed native code; it includes all range and mathematical candidate checks. -/
def firstSuccessStep {R S : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S) :
    StructuredCalls.Cmd R S :=
  .ite found (.base .skip)
    (.seq check (.ite accepted
      (.seq (.call (StackRoutines.copyProgram current selected scratch value present))
        (.base (.atom (.set found true)))) (.base .skip)))

/-- Later candidates still pay the branch, but never overwrite the witness. -/
theorem firstSuccessStep_skip {R S : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a : StructuredCalls.State R S) (hf : a.regs found = true) :
    StructuredCalls.Eval (firstSuccessStep check found accepted value present current selected scratch)
      1 a a :=
  .ite_true hf (.base (.skip a))

theorem firstSuccessStep_reject {R S n : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a b : StructuredCalls.State R S) (hf : a.regs found = false)
    (hc : StructuredCalls.Eval check n a b) (hno : b.regs accepted = false) :
    StructuredCalls.Eval (firstSuccessStep check found accepted value present current selected scratch)
      (n + 2) a b := by
  convert StructuredCalls.Eval.ite_false hf
    (StructuredCalls.Eval.seq hc (StructuredCalls.Eval.ite_false hno (.base (.skip b)))) using 1
  · rfl

/-- The successful case pays for copying the entire candidate into the saved
witness port. The temporary copy stack is empty again at return. -/
theorem firstSuccessStep_accept {R S n : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a b : StructuredCalls.State R S) (hf : a.regs found = false)
    (hc : StructuredCalls.Eval check n a b) (hyes : b.regs accepted = true)
    (hcs : current ≠ selected) (hct : current ≠ scratch) (hts : scratch ≠ selected)
    (hvp : value ≠ present) (ht : b.stacks scratch = []) (hs : b.stacks selected = []) :
    ∃ c : StructuredCalls.State R S,
      StructuredCalls.Eval (firstSuccessStep check found accepted value present current selected scratch)
        (n + 7 * (b.stacks current).length + 8) a c ∧
      c.regs found = true ∧ c.stacks selected = b.stacks current ∧
      (∀ i, i ≠ selected → c.stacks i = b.stacks i) := by
  let copied : StructuredCalls.State R S :=
    ⟨readRegs b.regs value present none, StackRoutines.copyStacks current selected b.stacks⟩
  have hcopy : StructuredCalls.Eval
      (.call (StackRoutines.copyProgram current selected scratch value present))
      (7 * (b.stacks current).length + 5) b copied :=
    .call _ (ListRegisterProgram.copy_run current selected scratch value present
      hcs hct hts hvp b.regs b.stacks ht)
  let c := (StructuredProgram.Atom.set (s := S) found true).eval copied
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · have h : StructuredCalls.Eval
        (firstSuccessStep check found accepted value present current selected scratch)
        (n + ((7 * (b.stacks current).length + 5 + 1) + 1) + 1) a c :=
      .ite_false hf (.seq hc (.ite_true hyes
        (.seq (n := 7 * (b.stacks current).length + 5) (m := 1)
          hcopy (.base (.atom _ _)))))
    simpa [Nat.add_assoc] using h
  · simp [c, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg]
  · simp [c, copied, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg,
      StackRoutines.copyStacks, hs]
  · intro i hi
    simp [c, copied, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg,
      StackRoutines.copyStacks, hi]

/-- Recover the witness flag from its physical stack on every invocation.
The saved tuple is nonempty even for the unique zero-dimensional candidate. -/
def firstSuccess {R S : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S) :
    StructuredCalls.Cmd R S :=
  .seq (.base (.atom (.peek selected value found)))
    (firstSuccessStep check found accepted value present current selected scratch)

theorem firstSuccess_saved {R S : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a : StructuredCalls.State R S) (hne : a.stacks selected ≠ []) :
    ∃ b, StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch) 2 a b ∧
      b.stacks = a.stacks := by
  let b := (StructuredProgram.Atom.peek selected value found).eval a
  have hb : b.regs found = true := by
    simp [b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg, readRegs,
      List.isSome_head?, hne]
  exact ⟨b, .seq (.base (.atom _ _))
    (firstSuccessStep_skip check found accepted value present current selected scratch b hb), rfl⟩

/-- A fresh selection invokes the real checker after the physical empty-stack
peek. This lemma exposes the success case to the outer iterator invariant. -/
theorem firstSuccess_fresh_accept {R S n : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a b : StructuredCalls.State R S) (ha : a.stacks selected = [])
    (hc : StructuredCalls.Eval check n
      ((StructuredProgram.Atom.peek selected value found).eval a) b)
    (hyes : b.regs accepted = true)
    (hcs : current ≠ selected) (hct : current ≠ scratch) (hts : scratch ≠ selected)
    (hvp : value ≠ present) (ht : b.stacks scratch = []) (hs : b.stacks selected = []) :
    ∃ c : StructuredCalls.State R S,
      StructuredCalls.Eval (firstSuccess check found accepted value present current selected scratch)
        (n + 7 * (b.stacks current).length + 9) a c ∧
      c.stacks selected = b.stacks current ∧
      (∀ i, i ≠ selected → c.stacks i = b.stacks i) := by
  let entry := (StructuredProgram.Atom.peek selected value found).eval a
  have hf : entry.regs found = false := by
    simp [entry, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg, readRegs, ha]
  obtain ⟨c, he, _, hselected, hframe⟩ := firstSuccessStep_accept check found accepted value present
    current selected scratch entry b hf hc hyes hcs hct hts hvp ht hs
  refine ⟨c, ?_, hselected, hframe⟩
  have h : StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch)
      (1 + (n + 7 * (b.stacks current).length + 8)) a c := .seq (.base (.atom _ _)) he
  convert h using 1
  omega

theorem firstSuccess_fresh_reject {R S n : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a b : StructuredCalls.State R S) (ha : a.stacks selected = [])
    (hc : StructuredCalls.Eval check n
      ((StructuredProgram.Atom.peek selected value found).eval a) b)
    (hno : b.regs accepted = false) :
    StructuredCalls.Eval (firstSuccess check found accepted value present current selected scratch)
      (n + 3) a b := by
  let entry := (StructuredProgram.Atom.peek selected value found).eval a
  have hf : entry.regs found = false := by
    simp [entry, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg, readRegs, ha]
  have he := firstSuccessStep_reject check found accepted value present current selected scratch
    entry b hf hc hno
  have h : StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch)
      (1 + (n + 2)) a b := .seq (.base (.atom _ _)) he
  convert h using 1
  omega

/-- Every real callback invocation performs exactly the first-success saved
word update. This connects native execution to the odometer's rank log. -/
theorem firstSuccess_update {R S n : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (acceptedRanks : ℕ → Bool) (encode : ℕ → List Bool) (rank : ℕ)
    (a c : StructuredCalls.State R S)
    (hcurrent : a.stacks current = encode rank)
    (hcs : current ≠ selected) (hct : current ≠ scratch) (hts : scratch ≠ selected)
    (hvp : value ≠ present)
    (hcheck : a.stacks selected = [] → ∃ m b,
      StructuredCalls.Eval check m
        ((StructuredProgram.Atom.peek selected value found).eval a) b ∧
      b.regs accepted = acceptedRanks rank ∧ b.stacks current = a.stacks current ∧
      b.stacks selected = [] ∧ b.stacks scratch = [])
    (heval : StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch) n a c) :
    c.stacks selected = saveFirst acceptedRanks encode (a.stacks selected) rank := by
  by_cases ha : a.stacks selected = []
  · obtain ⟨m, b, hc, hflag, hcounter, hselected, hscratch⟩ := hcheck ha
    cases hrank : acceptedRanks rank with
    | false =>
        have hb := firstSuccess_fresh_reject check found accepted value present current selected
          scratch a b ha hc (hflag.trans hrank)
        have heq := heval.final_unique current hb
        subst c
        simp [saveFirst, ha, hrank, hselected]
    | true =>
        obtain ⟨b', hb', hsaved, _⟩ := firstSuccess_fresh_accept check found accepted value
          present current selected scratch a b ha hc (hflag.trans hrank)
          hcs hct hts hvp hscratch hselected
        have heq := heval.final_unique current hb'
        subst c
        rw [hsaved, hcounter, hcurrent]
        simp [saveFirst, ha, hrank]
  · obtain ⟨b, hb, hframe⟩ := firstSuccess_saved check found accepted value present
      current selected scratch a ha
    have heq := heval.final_unique current hb
    subst c
    simp [saveFirst, List.isEmpty_iff, ha, hframe]

/-- Once a native callback has saved a witness, every subsequent callback
and odometer increment preserves those exact bytes. -/
theorem search_retains_selected {R S steps : ℕ} (ports : CounterForPrograms.Ports R S)
    (check : StructuredCalls.Cmd R S) (found accepted value present : Fin R)
    (selected copyScratch : Fin S) (hc : selected ≠ ports.counter)
    (hs : selected ≠ ports.scratch) {shape ranks : List ℕ}
    {a b : StructuredCalls.State R S}
    (visits : ExecCNFTupleEnumeration.Visits ports
      (firstSuccess check found accepted value present ports.counter selected copyScratch)
      shape ranks steps a b) (hne : a.stacks selected ≠ []) :
    b.stacks selected = a.stacks selected := by
  induction visits with
  | done => rfl
  | @step words start middle finish nb na nt ranks hflag hshape hcounter hbody
      hpreserve hadvance tail ih =>
      obtain ⟨out, hout, hframe⟩ := firstSuccess_saved check found accepted value present
        ports.counter selected copyScratch start hne
      have heq := hbody.final_unique ports.counter hout
      have hmiddle : middle.stacks selected = start.stacks selected := by
        rw [heq, hframe]
      have hnext := ExecCNFTupleEnumeration.advanceResult_outside ports middle words selected hc hs
      rw [ih (by rw [← hnext, hmiddle]; exact hne), ← hnext, hmiddle]

/-- A covered successful candidate forces a nonempty native result. This
uses the actual occurrence and its remaining execution, without choosing an
abstract matrix or materializing a family of candidates. -/
theorem search_reaches_success {R S steps : ℕ} (ports : CounterForPrograms.Ports R S)
    (check : StructuredCalls.Cmd R S) (found accepted value present : Fin R)
    (selected copyScratch : Fin S) (hc : selected ≠ ports.counter)
    (hs : selected ≠ ports.scratch) {shape ranks : List ℕ}
    {a b : StructuredCalls.State R S}
    (visits : ExecCNFTupleEnumeration.Visits ports
      (firstSuccess check found accepted value present ports.counter selected copyScratch)
      shape ranks steps a b) (I : StructuredCalls.State R S → Prop) (hi : I a)
    (hcallback : ∀ words start finish cost, words.map List.length = shape →
      start.stacks ports.counter = Encoding.encodeList id words →
      StructuredCalls.Eval
        (firstSuccess check found accepted value present ports.counter selected copyScratch)
        cost start finish → I start → I finish)
    (hnext : ∀ words start, I start → I (ExecCNFTupleEnumeration.advanceResult ports start words))
    (target : List (List Bool)) (htarget : target.map List.length = shape)
    (hmember : CounterPrograms.value target.flatten ∈ ranks)
    (hsuccess : ∀ start finish cost,
      start.stacks ports.counter = Encoding.encodeList id target →
      StructuredCalls.Eval
        (firstSuccess check found accepted value present ports.counter selected copyScratch)
        cost start finish → I start → finish.stacks selected ≠ []) :
    b.stacks selected ≠ [] := by
  induction visits with
  | done => simp at hmember
  | @step words start middle finish nb na nt ranks hflag hshape hcounter hbody
      hpreserve hadvance tail ih =>
      have hmiddle := hcallback words start middle nb hshape hcounter hbody hi
      rcases List.mem_cons.mp hmember with hhead | htail
      · have hwords : words = target := ExecCNFTupleEnumeration.tuple_eq_of_shape_value
          (hshape.trans htarget.symm) hhead.symm
        have hselected := hsuccess start middle nb (by simpa [hwords] using hcounter) hbody hi
        have hout := search_retains_selected ports check found accepted value present
          selected copyScratch hc hs tail (by
            rw [← ExecCNFTupleEnumeration.advanceResult_outside ports middle words selected hc hs]
            exact hselected)
        rw [hout, ← ExecCNFTupleEnumeration.advanceResult_outside ports middle words selected hc hs]
        exact hselected
      · exact ih (hnext words middle hmiddle) htail

/-- Full fixed-control scan, with each failed matrix, post-success branch and
final odometer reset charged. The invariant is a concrete checker contract. -/
theorem search_runs {R S : ℕ} (ports : CounterForPrograms.Ports R S)
    (check : StructuredCalls.Cmd R S) (found accepted value present : Fin R)
    (selected copyScratch : Fin S) (d budget : ℕ)
    (I : StructuredCalls.State R S → Prop)
    (stable : CounterForPrograms.FrameStable ports (fun _ => I))
    (spec : ExecCNFTupleEnumeration.BodySpec ports
      (firstSuccess check found accepted value present ports.counter selected copyScratch)
      (List.replicate d 2) I budget)
    (a : StructuredCalls.State R S) (hi : I a)
    (hc : a.stacks ports.counter =
      Encoding.encodeList id (List.replicate d [false, false]))
    (hs : a.stacks ports.scratch = []) :
    ∃ b, I b ∧ RunsIn (ExecCNFTupleEnumeration.program ports
      (firstSuccess check found accepted value present ports.counter selected copyScratch))
      (4 ^ d * (budget + 42 * d + 12) + 3)
      (a.withPC (some (ExecCNFTupleEnumeration.program ports
        (firstSuccess check found accepted value present ports.counter selected copyScratch)).entry))
      (b.withPC none) := by
  obtain ⟨b, hb, ht⟩ := ExecCNFTupleEnumeration.program_runs ports
    (firstSuccess check found accepted value present ports.counter selected copyScratch)
    (List.replicate d 2) I budget stable spec (List.replicate d [false, false]) a
    (by simp) hi hc hs (ExecCNFTupleEnumeration.zero_tuple_value d 2)
  refine ⟨b, hb, ?_⟩
  have hlen : (List.replicate d [false, false]).flatten.length = 2 * d := by simp [Nat.mul_comm]
  have henc : (Encoding.encodeList id (List.replicate d [false, false])).length = 6 * d + 1 := by
    rw [ExecCNFTupleOdometer.encoded_length, hlen]
    simp
    omega
  rw [hlen, henc] at ht
  have hpow : 2 ^ (2 * d) = 4 ^ d := by rw [pow_mul]; norm_num
  rw [hpow] at ht
  have hbudget : budget + 7 * (6 * d + 1) + 5 = budget + 42 * d + 12 := by omega
  simpa only [hbudget] using ht

/-- Selection composes the checker's uniform prefix bound with only a local
linear-time copy. The checker may run for exponentially many steps. -/
theorem firstSuccess_fresh_space {R S n B : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a b : StructuredCalls.State R S) (ha : a.stacks selected = [])
    (hc : StructuredCalls.Eval check n
      ((StructuredProgram.Atom.peek selected value found).eval a) b)
    (hchecker : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled check current selected) prefixSteps
        (((StructuredProgram.Atom.peek selected value found).eval a).withPC
          (some (StructuredCalls.compiled check current selected).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ B)
    (hcs : current ≠ selected) (hct : current ≠ scratch) (hts : scratch ≠ selected)
    (hvp : value ≠ present) (ht : b.stacks scratch = []) :
    ∃ steps c, StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch) steps a c ∧
      steps ≤ n + 7 * B + 10 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (StructuredCalls.compiled
          (firstSuccess check found accepted value present current selected scratch) current selected)
          prefixSteps (a.withPC (some (StructuredCalls.compiled
            (firstSuccess check found accepted value present current selected scratch)
            current selected).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ S * B + 8 * B + 10 := by
  let entry := (StructuredProgram.Atom.peek selected value found).eval a
  let save : StructuredCalls.Cmd R S :=
    .seq (.call (StackRoutines.copyProgram current selected scratch value present))
      (.base (.atom (.set found true)))
  let post : StructuredCalls.Cmd R S := .ite accepted save (.base .skip)
  let bound := S * B + 8 * B + 10
  have hB : B ≤ bound := by dsimp [bound]; omega
  have hb : ∀ i, (b.stacks i).length ≤ B :=
    hchecker n _ (Nat.le_refl _) (StructuredCalls.compiled_trace hc current selected)
  have hpost : ∃ m c, StructuredCalls.Eval post m b c ∧ m ≤ 7 * B + 7 := by
    cases hy : b.regs accepted with
    | false => exact ⟨1, b, .ite_false hy (.base (.skip b)), by omega⟩
    | true =>
      let copied : StructuredCalls.State R S :=
        ⟨readRegs b.regs value present none, StackRoutines.copyStacks current selected b.stacks⟩
      have hcopy : StructuredCalls.Eval
          (.call (StackRoutines.copyProgram current selected scratch value present))
          (7 * (b.stacks current).length + 5) b copied :=
        .call _ (ListRegisterProgram.copy_run current selected scratch value present
          hcs hct hts hvp b.regs b.stacks ht)
      let c := (StructuredProgram.Atom.set (s := S) found true).eval copied
      refine ⟨(7 * (b.stacks current).length + 5 + 1) + 1, c,
        .ite_true hy (.seq (n := 7 * (b.stacks current).length + 5) (m := 1)
          hcopy (.base (.atom _ _))), ?_⟩
      have hi := hb current
      omega
  obtain ⟨m, c, hpost, hm⟩ := hpost
  have postBound : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (StructuredCalls.compiled post current selected) prefixSteps
        (b.withPC (some (StructuredCalls.compiled post current selected).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle htrace i
    have hinit : dataBits (b.withPC (some (StructuredCalls.compiled post current selected).entry)) ≤
        S * B := StreamResources.dataBits_le_mul _ hb
    have h := StructuredSpace.local_stack_bound (StructuredCalls.compiled post current selected)
      (steps := 7 * B + 7) hinit prefixSteps intermediate (hle.trans hm) htrace i
    dsimp [bound]
    omega
  have checkBound : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled check current selected) prefixSteps
        (entry.withPC (some (StructuredCalls.compiled check current selected).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle htrace i
    exact (hchecker prefixSteps intermediate hle htrace i).trans hB
  have hseq := StructuredSpace.sequence_stack_bound hc hpost current selected checkBound postBound
    (StructuredCalls.compiled (.seq check post) current selected)
    (StructuredCalls.siteAddress (.seq check post)) (StructuredCalls.exitAddress (.seq check post))
    (StructuredCalls.compiled_site _ current selected)
  have hf : entry.regs found = false := by
    simp [entry, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg, readRegs, ha]
  have hselect : StructuredCalls.Eval
      (firstSuccessStep check found accepted value present current selected scratch)
      (n + m + 1) entry c := .ite_false hf (.seq hc hpost)
  have selectBound := StructuredSpace.conditional_false_stack_bound hf (.seq hc hpost)
    current selected hseq
    (StructuredCalls.compiled
      (firstSuccessStep check found accepted value present current selected scratch) current selected)
    (StructuredCalls.siteAddress
      (firstSuccessStep check found accepted value present current selected scratch))
    (StructuredCalls.exitAddress
      (firstSuccessStep check found accepted value present current selected scratch))
    (StructuredCalls.compiled_site _ current selected)
  let peek : StructuredCalls.Cmd R S := .base (.atom (.peek selected value found))
  have hp : StructuredCalls.Eval peek 1 a entry := .base (.atom _ _)
  have peekBound : ∀ prefixSteps intermediate, prefixSteps ≤ 1 →
      Trace (StructuredCalls.compiled peek current selected) prefixSteps
        (a.withPC (some (StructuredCalls.compiled peek current selected).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle htrace i
    have hinitial : ∀ i, (a.stacks i).length ≤ B := hchecker 0 _ (Nat.zero_le _) (.refl _)
    have hinit : dataBits (a.withPC (some (StructuredCalls.compiled peek current selected).entry)) ≤
        S * B := StreamResources.dataBits_le_mul _ hinitial
    have h := StructuredSpace.local_stack_bound (StructuredCalls.compiled peek current selected)
      (steps := 1) hinit prefixSteps intermediate hle htrace i
    dsimp [bound]
    omega
  refine ⟨1 + (n + m + 1), c, .seq hp hselect, by omega, ?_⟩
  exact StructuredSpace.sequence_stack_bound hp hselect current selected peekBound selectBound
    (StructuredCalls.compiled
      (firstSuccess check found accepted value present current selected scratch) current selected)
    (StructuredCalls.siteAddress
      (firstSuccess check found accepted value present current selected scratch))
    (StructuredCalls.exitAddress
      (firstSuccess check found accepted value present current selected scratch))
    (StructuredCalls.compiled_site _ current selected)

/-- Later visits retain the first witness with constant time and bounded
space, even though the odometer still traverses the remaining ranks. -/
theorem firstSuccess_saved_space {R S B : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a : StructuredCalls.State R S) (hne : a.stacks selected ≠ [])
    (hinitial : ∀ i, (a.stacks i).length ≤ B) :
    ∃ b, StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch) 2 a b ∧
      b.stacks = a.stacks ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ 2 →
        Trace (StructuredCalls.compiled
          (firstSuccess check found accepted value present current selected scratch) current selected)
          prefixSteps (a.withPC (some (StructuredCalls.compiled
            (firstSuccess check found accepted value present current selected scratch)
            current selected).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ S * B + 8 * B + 10 := by
  obtain ⟨b, heval, hframe⟩ := firstSuccess_saved check found accepted value present
    current selected scratch a hne
  refine ⟨b, heval, hframe, ?_⟩
  intro prefixSteps intermediate hle htrace i
  have hinit : dataBits (a.withPC (some (StructuredCalls.compiled
      (firstSuccess check found accepted value present current selected scratch)
      current selected).entry)) ≤ S * B := StreamResources.dataBits_le_mul _ hinitial
  have h := StructuredSpace.local_stack_bound (StructuredCalls.compiled
    (firstSuccess check found accepted value present current selected scratch) current selected)
    (steps := 2) hinit prefixSteps intermediate hle htrace i
  omega


/-- Fixed caller ports: dimension, consumed copy, current tuple, copy scratch,
and one-bit rejection latch. The embedding is chosen before any input. -/
structure ScanPorts (S : ℕ) where
  stack : Fin 5 ↪ Fin S

def scanRegisters : Fin 4 ↪ Fin 16 := ⟨Fin.castAdd 12, Fin.castAdd_injective _ _⟩

def scanInitializePorts {S : ℕ} (p : ScanPorts S) : Fin 2 ↪ Fin S :=
  ⟨![p.stack 1, p.stack 2], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [p.stack.injective.eq_iff]⟩

def prepareScan {S : ℕ} (p : ScanPorts S) : StructuredCalls.Cmd 16 S :=
  .seq (.call (StackRoutines.copyProgram (p.stack 0) (p.stack 1) (p.stack 3) 0 1)) <|
  .seq (.call (ProgramLinking.liftProgram zeroTupleProgram scanRegisters (scanInitializePorts p))) <|
  .seq (.base (.atom (.set 13 false))) (.base (.atom (.push (p.stack 4) 13)))

/-- Preparing one streaming scan restores the dimension copy and scratch;
only the counter and the one-bit rejection latch are initialized. -/
theorem prepareScan_eval {S : ℕ} (p : ScanPorts S) (a : StructuredCalls.State 16 S)
    (hi : a.stacks (p.stack 1) = []) (hc : a.stacks (p.stack 2) = [])
    (hs : a.stacks (p.stack 3) = []) (hl : a.stacks (p.stack 4) = []) :
    ∃ b, StructuredCalls.Eval (prepareScan p) (15 * (a.stacks (p.stack 0)).length + 13) a b ∧
      b.stacks = Function.update
        (Function.update a.stacks (p.stack 2)
          (Encoding.encodeList id (List.replicate (a.stacks (p.stack 0)).length [false, false])))
        (p.stack 4) [false] := by
  let copied : StructuredCalls.State 16 S :=
    ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks (p.stack 0) (p.stack 1) a.stacks⟩
  have hcopy : StructuredCalls.Eval
      (.call (StackRoutines.copyProgram (p.stack 0) (p.stack 1) (p.stack 3) 0 1))
      (7 * (a.stacks (p.stack 0)).length + 5) a copied :=
    .call _ (ListRegisterProgram.copy_run _ _ _ _ _
      (p.stack.injective.ne (by decide)) (p.stack.injective.ne (by decide))
      (p.stack.injective.ne (by decide)) (by decide) a.regs a.stacks hs)
  have hcopied : copied.stacks (p.stack 1) = a.stacks (p.stack 0) := by
    simp [copied, StackRoutines.copyStacks, hi]
  have hcopiedFrame (i : Fin S) (hne : i ≠ p.stack 1) : copied.stacks i = a.stacks i := by
    simp [copied, StackRoutines.copyStacks, hne]
  have houtput : copied.stacks ((scanInitializePorts p) 1) = [] := by
    change copied.stacks (p.stack 2) = []
    exact (hcopiedFrame _ (p.stack.injective.ne (by decide))).trans hc
  obtain ⟨initialized, hinitialize, hempty, htuple, hframe, _⟩ :=
    initialize_call scanRegisters (scanInitializePorts p) copied houtput
  have hinitInput : initialized.stacks (p.stack 1) = [] := hempty
  have hinitCounter : initialized.stacks (p.stack 2) =
      Encoding.encodeList id (List.replicate (a.stacks (p.stack 0)).length [false, false]) := by
    change initialized.stacks (p.stack 2) = Encoding.encodeList id
      (List.replicate (copied.stacks (p.stack 1)).length [false, false]) at htuple
    simpa only [hcopied] using htuple
  have hinitFrame (i : Fin S) (h1 : i ≠ p.stack 1) (h2 : i ≠ p.stack 2) :
      initialized.stacks i = a.stacks i := by
    rw [hframe i (by
      rintro ⟨j, hj⟩
      fin_cases j
      · exact h1 hj.symm
      · exact h2 hj.symm)]
    exact hcopiedFrame i h1
  let flagged := (StructuredProgram.Atom.set (s := S) 13 false).eval initialized
  let b := (StructuredProgram.Atom.push (p.stack 4) (13 : Fin 16)).eval flagged
  have hseed : StructuredCalls.Eval
      (.seq (.base (.atom (.set 13 false))) (.base (.atom (.push (p.stack 4) 13))))
      2 initialized b := .seq (.base (.atom _ _)) (.base (.atom _ _))
  refine ⟨b, ?_, ?_⟩
  · have h := hcopy.seq (hinitialize.seq hseed)
    change StructuredCalls.Eval (prepareScan p)
      ((7 * (a.stacks (p.stack 0)).length + 5) +
        ((8 * (copied.stacks (p.stack 1)).length + 6) + 2)) a b at h
    rw [hcopied] at h
    convert h using 1
    omega
  · have hlatch : initialized.stacks (p.stack 4) = [] :=
      (hinitFrame _ (p.stack.injective.ne (by decide))
        (p.stack.injective.ne (by decide))).trans hl
    have hb : b.stacks = Function.update initialized.stacks (p.stack 4) [false] := by
      simp [b, flagged, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, hlatch]
    rw [hb]
    funext i
    by_cases h4 : i = p.stack 4
    · subst i; simp
    by_cases h2 : i = p.stack 2
    · subst i; simp [h4, hinitCounter]
    by_cases h1 : i = p.stack 1
    · subst i; simp [h4, h2, hinitInput, hi]
    · simp [h4, h2, hinitFrame i h1 h2]

/-- Read the actual rejection bit, negate it into the acceptance register,
and clear the current counter with all cleanup charged. -/
def finishScan {S : ℕ} (counter latch : Fin S) : StructuredCalls.Cmd 16 S :=
  .seq (.base (.atom (.pop latch 13 14))) <|
  .seq (.base (.atom (.bnot 15 13)))
    (.call (StackRoutines.clearProgram counter 0 1))

theorem finishScan_eval {S : ℕ} (counter latch : Fin S) (hcl : counter ≠ latch)
    (a : StructuredCalls.State 16 S) (rejected : Bool) (hl : a.stacks latch = [rejected]) :
    ∃ b, StructuredCalls.Eval (finishScan counter latch)
      (2 * (a.stacks counter).length + 5) a b ∧ b.regs 15 = !rejected ∧
      b.stacks = Function.update (Function.update a.stacks latch []) counter [] := by
  let popped := (StructuredProgram.Atom.pop latch (13 : Fin 16) 14).eval a
  let flagged := (StructuredProgram.Atom.bnot (s := S) (15 : Fin 16) 13).eval popped
  let b : StructuredCalls.State 16 S :=
    ⟨readRegs flagged.regs 0 1 none, StackRoutines.clearStacks counter flagged.stacks⟩
  have hcounter : flagged.stacks counter = a.stacks counter := by
    simp [flagged, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hcl]
  have hclear : StructuredCalls.Eval (.call (StackRoutines.clearProgram counter 0 1))
      (2 * (flagged.stacks counter).length + 3) flagged b :=
    .call _ (ListRegisterProgram.clear_run _ _ _ _ _)
  refine ⟨b, ?_, ?_, ?_⟩
  · have h := (StructuredCalls.Eval.base (.atom (.pop latch 13 14) a)).seq
      ((StructuredCalls.Eval.base (.atom (.bnot 15 13) popped)).seq hclear)
    rw [hcounter] at h
    convert h using 1
    · rfl
    · omega
  · simp [b, flagged, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs, hl]
  · simp [b, flagged, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      StackRoutines.clearStacks, hl]

def scanWrapper {S l : ℕ} (p : ScanPorts S) (core : Program 16 S l) : StructuredCalls.Cmd 16 S :=
  .seq (prepareScan p) (.seq (.call core) (finishScan (p.stack 2) (p.stack 4)))


/-- State assertion for preparation, not a free input-construction operation. -/
def scanPreparedStacks {S : ℕ} (p : ScanPorts S) (a : StructuredCalls.State 16 S) :
    Fin S → List Bool :=
  Function.update (Function.update a.stacks (p.stack 2)
    (Encoding.encodeList id (List.replicate (a.stacks (p.stack 0)).length [false, false])))
    (p.stack 4) [false]

/-- The native setup, complete core scan, actual Boolean readout and cleanup
form one measured run. Its storage uses the core's prefix bound, never the
core's possibly exponential running time. -/
theorem scanWrapper_resources {S l A B T : ℕ} (p : ScanPorts S) (core : Program 16 S l)
    (a : StructuredCalls.State 16 S) (rejected : Bool)
    (hi : a.stacks (p.stack 1) = []) (hc : a.stacks (p.stack 2) = [])
    (hs : a.stacks (p.stack 3) = []) (hl : a.stacks (p.stack 4) = [])
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hcore : ∀ prepared : StructuredCalls.State 16 S,
      prepared.stacks = scanPreparedStacks p a →
      ∃ (n : ℕ) (middle : StructuredCalls.State 16 S), n ≤ T ∧
        Trace core n (prepared.withPC (some core.entry)) (middle.withPC none) ∧
        middle.stacks (p.stack 4) = [rejected] ∧
        (∀ i, i ≠ p.stack 2 → i ≠ p.stack 4 → middle.stacks i = prepared.stacks i) ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ n →
          Trace core prefixSteps (prepared.withPC (some core.entry)) intermediate →
          ∀ i, (intermediate.stacks i).length ≤ B) :
    ∃ steps out, StructuredCalls.Eval (scanWrapper p core) steps a out ∧
      steps ≤ T + 15 * (a.stacks (p.stack 0)).length + 2 * B + 18 ∧
      out.regs 15 = !rejected ∧ out.stacks = a.stacks ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (StructuredCalls.compiled (scanWrapper p core) (p.stack 0) (p.stack 4))
          prefixSteps (a.withPC (some (StructuredCalls.compiled
            (scanWrapper p core) (p.stack 0) (p.stack 4)).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          S * A + 15 * (a.stacks (p.stack 0)).length + S * B + 3 * B + 18 := by
  obtain ⟨prepared, hprepare, hprepared⟩ := prepareScan_eval p a hi hc hs hl
  obtain ⟨n, middle, hn, htrace, hlatch, hframe, hspace⟩ := hcore prepared hprepared
  have hmiddle : ∀ i, (middle.stacks i).length ≤ B :=
    hspace n _ (Nat.le_refl _) htrace
  obtain ⟨out, hfinish, hanswer, hout⟩ := finishScan_eval (p.stack 2) (p.stack 4)
    (p.stack.injective.ne (by decide)) middle rejected hlatch
  have hcall : StructuredCalls.Eval (.call core) n prepared middle := .call _ htrace
  let bound := S * A + 15 * (a.stacks (p.stack 0)).length + S * B + 3 * B + 18
  have hprepareSpace : ∀ prefixSteps intermediate,
      prefixSteps ≤ 15 * (a.stacks (p.stack 0)).length + 13 →
      Trace (StructuredCalls.compiled (prepareScan p) (p.stack 0) (p.stack 4))
        prefixSteps (a.withPC (some (StructuredCalls.compiled
          (prepareScan p) (p.stack 0) (p.stack 4)).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle ht i
    have hinit : dataBits (a.withPC (some (StructuredCalls.compiled
        (prepareScan p) (p.stack 0) (p.stack 4)).entry)) ≤ S * A :=
      StreamResources.dataBits_le_mul _ ha
    have h := StructuredSpace.local_stack_bound
      (StructuredCalls.compiled (prepareScan p) (p.stack 0) (p.stack 4))
      (steps := 15 * (a.stacks (p.stack 0)).length + 13) hinit prefixSteps intermediate hle ht i
    dsimp [bound]
    omega
  have hcallSpace : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled (.call core) (p.stack 0) (p.stack 4)) prefixSteps
        (prepared.withPC (some (StructuredCalls.compiled
          (.call core) (p.stack 0) (p.stack 4)).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    have h := StructuredSpace.call_stack_bound core
      (StructuredCalls.compiled (.call core) (p.stack 0) (p.stack 4))
      (StructuredCalls.siteAddress (.call core)) (StructuredCalls.exitAddress (.call core))
      (fun pc => StructuredCalls.compiled_site (.call core) (p.stack 0) (p.stack 4) pc)
      htrace hspace
    intro prefixSteps intermediate hle ht i
    have hb := h prefixSteps intermediate hle ht i
    dsimp [bound]
    omega
  have hfinishSpace : ∀ prefixSteps intermediate,
      prefixSteps ≤ 2 * (middle.stacks (p.stack 2)).length + 5 →
      Trace (StructuredCalls.compiled (finishScan (p.stack 2) (p.stack 4)) (p.stack 0) (p.stack 4))
        prefixSteps (middle.withPC (some (StructuredCalls.compiled
          (finishScan (p.stack 2) (p.stack 4)) (p.stack 0) (p.stack 4)).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle ht i
    have hinit : dataBits (middle.withPC (some (StructuredCalls.compiled
        (finishScan (p.stack 2) (p.stack 4)) (p.stack 0) (p.stack 4)).entry)) ≤ S * B :=
      StreamResources.dataBits_le_mul _ hmiddle
    have h := StructuredSpace.local_stack_bound
      (StructuredCalls.compiled (finishScan (p.stack 2) (p.stack 4)) (p.stack 0) (p.stack 4))
      (steps := 2 * B + 5) hinit prefixSteps intermediate (by have := hmiddle (p.stack 2); omega) ht i
    dsimp [bound]
    omega
  refine ⟨(15 * (a.stacks (p.stack 0)).length + 13) +
    (n + (2 * (middle.stacks (p.stack 2)).length + 5)), out,
    hprepare.seq (hcall.seq hfinish), ?_, hanswer, ?_, ?_⟩
  · have := hmiddle (p.stack 2)
    omega
  · rw [hout]
    funext i
    by_cases h2 : i = p.stack 2
    · subst i; simp [hc]
    by_cases h4 : i = p.stack 4
    · subst i; simp [h2, hl]
    simp only [Function.update_of_ne h2, Function.update_of_ne h4]
    rw [hframe i h2 h4, hprepared]
    simp [h2, h4]
  · have hseq := StructuredSpace.sequence_stack_bound hcall hfinish (p.stack 0) (p.stack 4)
      hcallSpace hfinishSpace
      (StructuredCalls.compiled (.seq (.call core) (finishScan (p.stack 2) (p.stack 4)))
        (p.stack 0) (p.stack 4))
      (StructuredCalls.siteAddress (.seq (.call core) (finishScan (p.stack 2) (p.stack 4))))
      (StructuredCalls.exitAddress (.seq (.call core) (finishScan (p.stack 2) (p.stack 4))))
      (StructuredCalls.compiled_site _ (p.stack 0) (p.stack 4))
    exact StructuredSpace.sequence_stack_bound hprepare (hcall.seq hfinish) (p.stack 0) (p.stack 4)
      hprepareSpace hseq
      (StructuredCalls.compiled (scanWrapper p core) (p.stack 0) (p.stack 4))
      (StructuredCalls.siteAddress (scanWrapper p core))
      (StructuredCalls.exitAddress (scanWrapper p core))
      (StructuredCalls.compiled_site _ (p.stack 0) (p.stack 4))


/-- Outer-search ports are dimension, consumed copy, current tuple, and copy
scratch. No saved-witness sentinel is seeded by this initializer. -/
def searchInitializePorts {S : ℕ} (ports : Fin 4 ↪ Fin S) : Fin 2 ↪ Fin S :=
  ⟨![ports 1, ports 2], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [ports.injective.eq_iff]⟩

def prepareSearch {S : ℕ} (ports : Fin 4 ↪ Fin S) : StructuredCalls.Cmd 16 S :=
  .seq (.call (StackRoutines.copyProgram (ports 0) (ports 1) (ports 3) 0 1))
    (.call (ProgramLinking.liftProgram zeroTupleProgram scanRegisters
      (searchInitializePorts ports)))

/-- Runtime preparation retains one bounded-width tuple, including the
one-bit terminator when the matrix has zero entries. All other stacks survive. -/
theorem prepareSearch_eval {S : ℕ} (ports : Fin 4 ↪ Fin S)
    (a : StructuredCalls.State 16 S)
    (hi : a.stacks (ports 1) = []) (hc : a.stacks (ports 2) = [])
    (hs : a.stacks (ports 3) = []) :
    ∃ b, StructuredCalls.Eval (prepareSearch ports)
        (15 * (a.stacks (ports 0)).length + 11) a b ∧
      b.stacks = Function.update a.stacks (ports 2)
        (Encoding.encodeList id (List.replicate (a.stacks (ports 0)).length [false, false])) := by
  let copied : StructuredCalls.State 16 S :=
    ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks (ports 0) (ports 1) a.stacks⟩
  have hcopy : StructuredCalls.Eval
      (.call (StackRoutines.copyProgram (ports 0) (ports 1) (ports 3) 0 1))
      (7 * (a.stacks (ports 0)).length + 5) a copied :=
    .call _ (ListRegisterProgram.copy_run _ _ _ _ _
      (ports.injective.ne (by decide)) (ports.injective.ne (by decide))
      (ports.injective.ne (by decide)) (by decide) a.regs a.stacks hs)
  have hcopied : copied.stacks (ports 1) = a.stacks (ports 0) := by
    simp [copied, StackRoutines.copyStacks, hi]
  have hcopiedFrame (i : Fin S) (hne : i ≠ ports 1) : copied.stacks i = a.stacks i := by
    simp [copied, StackRoutines.copyStacks, hne]
  have houtput : copied.stacks ((searchInitializePorts ports) 1) = [] := by
    change copied.stacks (ports 2) = []
    exact (hcopiedFrame _ (ports.injective.ne (by decide))).trans hc
  obtain ⟨b, hinit, hempty, htuple, hframe, _⟩ :=
    initialize_call scanRegisters (searchInitializePorts ports) copied houtput
  refine ⟨b, ?_, ?_⟩
  · have h := hcopy.seq hinit
    change StructuredCalls.Eval (prepareSearch ports)
      ((7 * (a.stacks (ports 0)).length + 5) +
        (8 * (copied.stacks (ports 1)).length + 6)) a b at h
    rw [hcopied] at h
    convert h using 1
    omega
  · have hcounter : b.stacks (ports 2) = Encoding.encodeList id
        (List.replicate (a.stacks (ports 0)).length [false, false]) := by
      change b.stacks (ports 2) = Encoding.encodeList id
        (List.replicate (copied.stacks (ports 1)).length [false, false]) at htuple
      simpa only [hcopied] using htuple
    have hinput : b.stacks (ports 1) = [] := hempty
    funext i
    by_cases h2 : i = ports 2
    · subst i
      simpa using hcounter
    by_cases h1 : i = ports 1
    · subst i
      simp [h2, hinput, hi]
    · rw [Function.update_of_ne h2, hframe i (by
        rintro ⟨j, hj⟩
        fin_cases j
        · exact h1 hj.symm
        · exact h2 hj.symm)]
      exact hcopiedFrame i h1

/-- Every preparation prefix is bounded by retained input plus linear local
work; no exponential search budget enters this space estimate. -/
theorem prepareSearch_space {S A : ℕ} (ports : Fin 4 ↪ Fin S)
    (a : StructuredCalls.State 16 S) (ha : ∀ i, (a.stacks i).length ≤ A) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 15 * (a.stacks (ports 0)).length + 11 →
      Trace (StructuredCalls.compiled (prepareSearch ports) (ports 0) (ports 2))
        prefixSteps (a.withPC (some (StructuredCalls.compiled
          (prepareSearch ports) (ports 0) (ports 2)).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ S * A + 15 * (a.stacks (ports 0)).length + 11 := by
  intro prefixSteps intermediate hle ht i
  have hi : dataBits (a.withPC (some (StructuredCalls.compiled
      (prepareSearch ports) (ports 0) (ports 2)).entry)) ≤ S * A :=
    StreamResources.dataBits_le_mul _ ha
  exact StructuredSpace.local_stack_bound _ hi prefixSteps intermediate hle ht i


/-- Complete actual first-success traversal with both resources on its trace.
The callback contract is discharged by the concrete candidate checker; its
uniform prefix bound, rather than its running time, controls loop storage. -/
theorem search_resources {R S : ℕ} (ports : CounterForPrograms.Ports R S)
    (check : StructuredCalls.Cmd R S) (found accepted value present : Fin R)
    (selected copyScratch : Fin S) (d budget boundaryBound callbackBound : ℕ)
    (I : StructuredCalls.State R S → Prop)
    (stable : CounterForPrograms.FrameStable ports (fun _ => I))
    (spec : ExecCNFTupleEnumeration.BodySpec ports
      (firstSuccess check found accepted value present ports.counter selected copyScratch)
      (List.replicate d 2) I budget)
    (hcallback : ∀ words a b nb, words.map List.length = List.replicate d 2 →
      I a → (∀ i, (a.stacks i).length ≤ boundaryBound) →
      a.stacks ports.counter = Encoding.encodeList id words → a.stacks ports.scratch = [] →
      StructuredCalls.Eval
        (firstSuccess check found accepted value present ports.counter selected copyScratch)
        nb a b →
      (∀ i, (b.stacks i).length ≤ boundaryBound) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ nb →
        Trace (StructuredCalls.compiled
          (firstSuccess check found accepted value present ports.counter selected copyScratch)
          ports.counter ports.counter) prefixSteps
          (a.withPC (some (StructuredCalls.compiled
            (firstSuccess check found accepted value present ports.counter selected copyScratch)
            ports.counter ports.counter).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ callbackBound)
    (a : StructuredCalls.State R S) (hi : I a)
    (ha : ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hc : a.stacks ports.counter =
      Encoding.encodeList id (List.replicate d [false, false]))
    (hs : a.stacks ports.scratch = []) :
    ∃ steps out, I out ∧ out.stacks ports.scratch = [] ∧
      out.stacks ports.counter = Encoding.encodeList id (List.replicate d [false, false]) ∧
      steps ≤ 4 ^ d * (budget + 42 * d + 12) + 3 ∧
      Trace (ExecCNFTupleEnumeration.program ports
        (firstSuccess check found accepted value present ports.counter selected copyScratch))
        steps (a.withPC (some (ExecCNFTupleEnumeration.program ports
          (firstSuccess check found accepted value present ports.counter selected copyScratch)).entry))
        (out.withPC none) ∧
      (∃ loopSteps, steps = 1 + loopSteps + 1 ∧
        ExecCNFTupleEnumeration.Visits ports
          (firstSuccess check found accepted value present ports.counter selected copyScratch)
          (List.replicate d 2) (List.range' 0 (4 ^ d)) loopSteps
          (ExecCNFTupleEnumeration.startResult ports a) out) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (ExecCNFTupleEnumeration.program ports
          (firstSuccess check found accepted value present ports.counter selected copyScratch))
          prefixSteps (a.withPC (some (ExecCNFTupleEnumeration.program ports
            (firstSuccess check found accepted value present ports.counter selected copyScratch)).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤
            max callbackBound (S * boundaryBound + 7 * (6 * d + 1) + 4) := by
  let body := firstSuccess check found accepted value present ports.counter selected copyScratch
  obtain ⟨n, out, he, hv, ho, _, houtScratch, hn⟩ :=
    ExecCNFTupleEnumeration.enumerate_correct ports body (List.replicate d 2) I budget
      stable spec (List.replicate d [false, false]) a (by simp) hi hc hs
      (ExecCNFTupleEnumeration.zero_tuple_value d 2)
  have hp : 2 ^ (List.replicate d [false, false]).flatten.length = 4 ^ d := by
    simp only [List.length_flatten, List.map_replicate, List.length_cons, List.length_nil,
      List.sum_replicate, smul_eq_mul]
    change 2 ^ (d * 2) = 4 ^ d
    rw [Nat.mul_comm d 2, pow_mul]
    norm_num
  have hlen : (Encoding.encodeList id (List.replicate d [false, false])).length = 6 * d + 1 := by
    rw [Enumerators.encoded_shape_length (by simp :
      (List.replicate d [false, false]).map List.length = List.replicate d 2)]
    simp
    omega
  let J : StructuredCalls.State R S → Prop := fun state => I state ∧
    (∀ i, (state.stacks i).length ≤ boundaryBound) ∧ state.stacks ports.scratch = []
  have hj : J (ExecCNFTupleEnumeration.startResult ports a) :=
    ⟨stable 0 a _ (fun _ _ _ => rfl) hi, ha, hs⟩
  have hloop := Enumerators.visits_stack_bound ports body (List.replicate d 2)
    J J boundaryBound callbackBound (fun _ h => h.2.1) (fun _ h => h.2.1)
    (by
      intro words start finish nb hw hcounter hbody hJ _
      obtain ⟨m, finish', _, hr, _, hs', hI'⟩ := spec words start hw hJ.1 hcounter hJ.2.2
      have heq := hbody.final_unique ports.counter hr
      subst finish'
      obtain ⟨hb, hprefix⟩ := hcallback words start finish nb hw hJ.1 hJ.2.1
        hcounter hJ.2.2 hbody
      exact ⟨⟨hI', hb, hs'⟩, hs', hprefix⟩)
    (by
      intro words state _ hcounter hJ
      refine ⟨stable 0 state _ (ExecCNFTupleEnumeration.advanceResult_outside ports state words)
        hJ.1, ?_, ExecCNFTupleEnumeration.advanceResult_scratch ports state words⟩
      intro i
      by_cases hcounterPort : i = ports.counter
      · subst i
        rw [ExecCNFTupleEnumeration.advanceResult_counter,
          ExecCNFTupleEnumeration.bumpWords_encoded_length, ← hcounter]
        exact hJ.2.1 ports.counter
      · by_cases hscratchPort : i = ports.scratch
        · subst i
          simp
        · rw [← ExecCNFTupleEnumeration.advanceResult_outside ports state words i
            hcounterPort hscratchPort]
          exact hJ.2.1 i)
    hv hj
  have hspace := Enumerators.enumerate_stack_bound ports body hv hloop
  have hreset := Enumerators.visits_reset_counter hv
    (ExecCNFTupleEnumeration.startResult_flag ports a)
  refine ⟨1 + n + 1, out, ho, houtScratch, ?_, ?_,
    StructuredCalls.compiled_halt_trace he ports.counter ports.counter, ?_, ?_⟩
  · simpa using hreset
  · rw [hp, hlen] at hn
    nlinarith
  · exact ⟨n, rfl, by simpa only [hp] using hv⟩
  · have hsize : 2 * (List.replicate d 2).sum +
        2 * (List.replicate d 2).length + 1 = 6 * d + 1 := by
      simp
      omega
    simpa only [hsize] using hspace


/-- Selection soundness refers to the physical retained matrix, not to an
arbitrary successful element of an abstract family. A preexisting witness is
unchanged; a fresh witness comes from the actual checker's acceptance bit. -/
theorem firstSuccess_matrix_sound {R S steps : ℕ} {Matrix : Type*}
    (check : StructuredCalls.Cmd R S) (found accepted value present : Fin R)
    (current selected scratch matrix : Fin S)
    (valid : Matrix → Prop) (encode : Matrix → List Bool)
    (a out : StructuredCalls.State R S)
    (hcs : current ≠ selected) (hct : current ≠ scratch) (hts : scratch ≠ selected)
    (hvp : value ≠ present) (hms : matrix ≠ selected)
    (hold : a.stacks selected ≠ [] → ∃ Q, valid Q ∧ a.stacks matrix = encode Q)
    (hcheck : a.stacks selected = [] → ∃ n b,
      StructuredCalls.Eval check n
        ((StructuredProgram.Atom.peek selected value found).eval a) b ∧
      b.stacks selected = [] ∧ b.stacks scratch = [] ∧
      (b.regs accepted = true → ∃ Q, valid Q ∧ b.stacks matrix = encode Q))
    (heval : StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch) steps a out) :
    out.stacks selected ≠ [] → ∃ Q, valid Q ∧ out.stacks matrix = encode Q := by
  by_cases ha : a.stacks selected = []
  · obtain ⟨n, b, hc, hs, ht, hvalid⟩ := hcheck ha
    cases hf : b.regs accepted with
    | false =>
        have hr := firstSuccess_fresh_reject check found accepted value present
          current selected scratch a b ha hc hf
        have heq := heval.final_unique current hr
        subst out
        exact fun h => (h hs).elim
    | true =>
        obtain ⟨c, hr, _, hframe⟩ := firstSuccess_fresh_accept check found accepted value present
          current selected scratch a b ha hc hf hcs hct hts hvp ht hs
        have heq := heval.final_unique current hr
        subst out
        intro _
        obtain ⟨Q, hQ, hmatrix⟩ := hvalid hf
        exact ⟨Q, hQ, (hframe matrix hms).trans hmatrix⟩
  · obtain ⟨b, hb, hframe⟩ := firstSuccess_saved check found accepted value present
      current selected scratch a ha
    have heq := heval.final_unique current hb
    subst out
    intro _
    obtain ⟨Q, hQ, hmatrix⟩ := hold ha
    exact ⟨Q, hQ, by rw [hframe]; exact hmatrix⟩


/-- Every callback boundary retains the same polynomial word bound. Only the
matrix being tested and the saved candidate may change; all caller words and
the counter survive selection exactly. -/
theorem firstSuccess_frame {R S steps B : ℕ}
    (check : StructuredCalls.Cmd R S) (found accepted value present : Fin R)
    (current selected scratch matrix : Fin S) (a out : StructuredCalls.State R S)
    (hcs : current ≠ selected) (hct : current ≠ scratch) (hts : scratch ≠ selected)
    (hvp : value ≠ present) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hcheck : a.stacks selected = [] → ∃ n b,
      StructuredCalls.Eval check n
        ((StructuredProgram.Atom.peek selected value found).eval a) b ∧
      b.stacks selected = [] ∧ b.stacks scratch = [] ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      (∀ i, i ≠ matrix → b.stacks i = a.stacks i))
    (heval : StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch) steps a out) :
    (∀ i, (out.stacks i).length ≤ B) ∧
      ∀ i, i ≠ matrix → i ≠ selected → out.stacks i = a.stacks i := by
  by_cases hs : a.stacks selected = []
  · obtain ⟨n, b, hc, hbselected, hbscratch, hb, hframe⟩ := hcheck hs
    cases hf : b.regs accepted with
    | false =>
        have hr := firstSuccess_fresh_reject check found accepted value present
          current selected scratch a b hs hc hf
        have heq := heval.final_unique current hr
        subst out
        exact ⟨hb, fun i hm _ => hframe i hm⟩
    | true =>
        obtain ⟨c, hr, hselected, hcframe⟩ := firstSuccess_fresh_accept check found accepted value
          present current selected scratch a b hs hc hf hcs hct hts hvp hbscratch hbselected
        have heq := heval.final_unique current hr
        subst out
        refine ⟨?_, fun i hm hsel => (hcframe i hsel).trans (hframe i hm)⟩
        intro i
        by_cases hsel : i = selected
        · subst i
          rw [hselected]
          exact hb current
        · rw [hcframe i hsel]
          exact hb i
  · obtain ⟨b, hb, hframe⟩ := firstSuccess_saved check found accepted value present
      current selected scratch a hs
    have heq := heval.final_unique current hb
    subst out
    exact ⟨fun i => by rw [hframe]; exact ha i, fun i _ _ => congrFun hframe i⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram
