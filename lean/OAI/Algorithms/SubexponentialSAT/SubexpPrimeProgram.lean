import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.CounterPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpPackingParameters
import OAI.Algorithms.SubexponentialSAT.ModularDivisionPrograms

namespace OAI.Algorithms

/-!
# Executable pieces of prime trial division

The numeric trial-division functions in the first section are specifications.
They are never instructions of a program. The executable zero test and Boolean
accumulator below contain only existing finite Boolean-stack instructions.
Candidate numbers, divisors, and remainders are runtime data.
-/

namespace SubexponentialSAT.SubexpPrimeProgram

open BitProgram StructuredProgram StructuredCalls

/-- Actual structured executions have a unique final data state.  The proof
uses the verified compiler and deterministic terminal configurations. -/
theorem eval_result_unique {R S : ℕ} {cmd : StructuredCalls.Cmd R S}
    {n m : ℕ} {a b c : StructuredProgram.State R S}
    (h₁ : StructuredCalls.Eval cmd n a b)
    (h₂ : StructuredCalls.Eval cmd m a c) (input output : Fin S) : b = c := by
  have t₁ := StructuredCalls.compiled_halt_trace h₁ input output
  have t₂ := StructuredCalls.compiled_halt_trace h₂ input output
  have hb : BitProgram.step (StructuredCalls.compiled cmd input output)
      (b.withPC none) = none := rfl
  have hc : BitProgram.step (StructuredCalls.compiled cmd input output)
      (c.withPC none) = none := rfl
  have heq := Computation.RunsIn.terminal_unique
    (show Computation.RunsIn _ (n + 1) _ _ from ⟨n + 1, le_rfl, t₁⟩)
    (show Computation.RunsIn _ (m + 1) _ _ from ⟨m + 1, le_rfl, t₂⟩) hb hc
  exact congrArg StructuredProgram.State.ofCfg heq

private theorem terminal_trace_steps_unique {α : Type*} {step : α → Option α}
    {n m : ℕ} {a b c : α} (h₁ : Computation.Trace step n a b)
    (h₂ : Computation.Trace step m a c) (hb : step b = none) (hc : step c = none) :
    n = m := by
  induction h₁ generalizing m c with
  | refl a =>
      cases h₂ with
      | refl => rfl
      | cons hs ht => simp [hb] at hs
  | @cons n a a' b hs ht ih =>
      cases h₂ with
      | refl => simp [hc] at hs
      | @cons m _ a'' c hs' ht' =>
          have haa : a' = a'' := Option.some.inj (hs.symm.trans hs')
          subst a''
          exact congrArg Nat.succ (ih ht' hb hc)

/-- The exact instruction count of a terminating structured execution is
unique as well as its result. This allows proved execution bounds to be used
for every actual occurrence of a subroutine in a larger trace. -/
theorem eval_steps_unique {R S : ℕ} {cmd : StructuredCalls.Cmd R S}
    {n m : ℕ} {a b c : StructuredProgram.State R S}
    (h₁ : StructuredCalls.Eval cmd n a b)
    (h₂ : StructuredCalls.Eval cmd m a c) (input output : Fin S) : n = m := by
  have h := terminal_trace_steps_unique
    (StructuredCalls.compiled_halt_trace h₁ input output)
    (StructuredCalls.compiled_halt_trace h₂ input output) rfl rfl
  omega

/-- Mathematical specification of testing a consecutive interval of divisors. -/
def trialFactors (candidate start : ℕ) : ℕ → Bool
  | 0 => true
  | fuel + 1 =>
      (!(decide (candidate % start = 0))) && trialFactors candidate (start + 1) fuel

theorem trialFactors_eq_all (candidate start fuel : ℕ) :
    trialFactors candidate start fuel =
      (List.range' start fuel).all (fun d => !(decide (candidate % d = 0))) := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih => simp only [trialFactors, List.range'_succ, List.all_cons, ih]

theorem trialFactors_true_iff (candidate start fuel : ℕ) :
    trialFactors candidate start fuel = true ↔
      ∀ d : ℕ, start ≤ d → d < start + fuel → candidate % d ≠ 0 := by
  induction fuel generalizing start with
  | zero => simp only [trialFactors, Nat.add_zero, true_iff]; intro d hlo hhi; omega
  | succ fuel ih =>
      simp only [trialFactors, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, ih]
      constructor
      · rintro ⟨hstart, hrest⟩ d hlo hhi
        by_cases hd : d = start
        · simpa [hd] using hstart
        · exact hrest d (by omega) (by omega)
      · intro h
        refine ⟨h start le_rfl (by omega), ?_⟩
        intro d hlo hhi
        exact h d (by omega) (by omega)

/-- Specification of complete trial division, including zero and one. -/
def trialPrime (candidate : ℕ) : Bool :=
  decide (2 ≤ candidate) && trialFactors candidate 2 (candidate - 2)

theorem trialPrime_true_iff (candidate : ℕ) :
    trialPrime candidate = true ↔ Nat.Prime candidate := by
  rw [trialPrime, Bool.and_eq_true, decide_eq_true_eq, trialFactors_true_iff]
  constructor
  · rintro ⟨hc, hdiv⟩
    by_contra hn
    obtain ⟨d, hd, hlo, hhi⟩ := (Nat.not_prime_iff_exists_dvd_lt hc).mp hn
    exact hdiv d hlo (by omega) (Nat.mod_eq_zero_of_dvd hd)
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    intro d hlo hhi hmod
    exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hmod) hlo
      (by omega) hp

/-- This identifies the trial-division specification with the old schedule's
prime predicate; it does not identify a numeric function with executable code. -/
theorem trialPrime_eq_primeTest (candidate : ℕ) :
    trialPrime candidate = SubexpPackingParameters.primeTest candidate := by
  apply Bool.eq_iff_iff.mpr
  simpa [SubexpPackingParameters.primeTest] using trialPrime_true_iff candidate

/-- Replacing the schedule's decidable predicate by the explicit finite divisor
scan preserves its mathematical prime-search result. -/
theorem scan_trialPrime_eq (start fuel : ℕ) :
    ParameterOrder.scanFrom trialPrime start fuel =
      ParameterOrder.scanFrom SubexpPackingParameters.primeTest start fuel := by
  have heq : trialPrime = SubexpPackingParameters.primeTest :=
    funext trialPrime_eq_primeTest
  rw [heq]

/-- Data state of the existing binary zero-test subroutine. -/
def zeroState (b p z : Bool) (word : List Bool) : StructuredProgram.State 3 2 :=
  ⟨CounterPrograms.counterRegs b p z, CounterPrograms.counterStacks word []⟩

/-- Complete zero-test trace, including its return/halt instruction, valid
for arbitrary incoming Boolean work registers. -/
theorem zero_terminal_trace (b p z : Bool) (word : List Bool) :
    BitProgram.Trace CounterPrograms.zeroProgram (8 * word.length + 6)
      ((zeroState b p z word).withPC (some CounterPrograms.zeroProgram.entry))
      ((zeroState false false (CounterPrograms.isZero word) word).withPC none) := by
  have hscan := CounterPrograms.zero_scan_trace b p true word []
  have hstart := Computation.Trace.cons (CounterPrograms.zero_step0 b p z word []) hscan
  have hactive :
      BitProgram.Trace CounterPrograms.zeroProgram (8 * word.length + 5)
        ((zeroState b p z word).withPC (some CounterPrograms.zeroProgram.entry))
        ((zeroState false false (CounterPrograms.isZero word) word).withPC (some 9)) := by
    simpa [zeroState, StructuredProgram.State.withPC, CounterPrograms.counterCfg,
      CounterPrograms.zeroProgram, Nat.add_assoc] using hstart
  have hhalt :
      BitProgram.Trace CounterPrograms.zeroProgram 1
        ((zeroState false false (CounterPrograms.isZero word) word).withPC (some 9))
        ((zeroState false false (CounterPrograms.isZero word) word).withPC none) := by
    refine .cons ?_ (.refl _)
    simp [BitProgram.step, BitProgram.execInstr,
      StructuredProgram.State.withPC]
  convert hactive.trans hhalt using 1

/-- Fixed finite zero-test program assigned caller-chosen, fixed ports. -/
abbrev zeroCheck {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 2 → Fin S) :
    StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram CounterPrograms.zeroProgram register stack)

theorem zeroCheck_eval {R S : ℕ}
    (register : Fin 3 → Fin R) (stack : Fin 2 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (frame : StructuredProgram.State R S) (b p z : Bool) (word : List Bool) :
    StructuredCalls.Eval (zeroCheck register stack) (8 * word.length + 6)
      (StructuredCalls.embedState register stack frame (zeroState b p z word))
      (StructuredCalls.embedState register stack frame
        (zeroState false false (CounterPrograms.isZero word) word)) :=
  StructuredCalls.eval_call_lifted CounterPrograms.zeroProgram register stack frame
    hregister hstack (zero_terminal_trace b p z word)

/-- Accumulate one trial result. A zero remainder makes the prime flag false.
Both Boolean operations and the zero-test call are concrete instructions. -/
abbrev recordTrial {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 2 → Fin S)
    (primeFlag : Fin R) : StructuredCalls.Cmd R S :=
  .seq (zeroCheck register stack)
    (.seq (.base (.atom (.bnot (register 2) (register 2))))
      (.base (.atom (.band primeFlag primeFlag (register 2)))))

noncomputable def recordTrialResult {R S : ℕ}
    (register : Fin 3 → Fin R) (stack : Fin 2 → Fin S)
    (primeFlag : Fin R) (frame : StructuredProgram.State R S) (word : List Bool) :
    StructuredProgram.State R S :=
  let checked := StructuredCalls.embedState register stack frame
    (zeroState false false (CounterPrograms.isZero word) word)
  let nonzero := (StructuredProgram.Atom.bnot (register 2) (register 2)).eval checked
  (StructuredProgram.Atom.band primeFlag primeFlag (register 2)).eval nonzero

theorem recordTrial_eval {R S : ℕ}
    (register : Fin 3 → Fin R) (stack : Fin 2 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (primeFlag : Fin R) (frame : StructuredProgram.State R S)
    (b p z : Bool) (word : List Bool) :
    StructuredCalls.Eval (recordTrial register stack primeFlag) (8 * word.length + 8)
      (StructuredCalls.embedState register stack frame (zeroState b p z word))
      (recordTrialResult register stack primeFlag frame word) := by
  have hz := zeroCheck_eval register stack hregister hstack frame b p z word
  have hn := StructuredCalls.Eval.base
    (StructuredProgram.Eval.atom (StructuredProgram.Atom.bnot (register 2) (register 2))
      (StructuredCalls.embedState register stack frame
        (zeroState false false (CounterPrograms.isZero word) word)))
  have ha := StructuredCalls.Eval.base
    (StructuredProgram.Eval.atom
      (StructuredProgram.Atom.band primeFlag primeFlag (register 2))
      ((StructuredProgram.Atom.bnot (register 2) (register 2)).eval
        (StructuredCalls.embedState register stack frame
          (zeroState false false (CounterPrograms.isZero word) word))))
  convert hz.seq (hn.seq ha) using 1
  · rfl

theorem recordTrialResult_flag {R S : ℕ}
    (register : Fin 3 → Fin R) (stack : Fin 2 → Fin S)
    (hregister : Function.Injective register)
    (primeFlag : Fin R) (hflag : ¬ ∃ i, register i = primeFlag)
    (frame : StructuredProgram.State R S) (word : List Bool) :
    (recordTrialResult register stack primeFlag frame word).regs primeFlag =
      (frame.regs primeFlag && !(CounterPrograms.isZero word)) := by
  have hne : primeFlag ≠ register 2 := by
    intro h
    exact hflag ⟨2, h.symm⟩
  have hp := StructuredCalls.embedState_register_frame register stack frame
    (zeroState false false (CounterPrograms.isZero word) word) primeFlag hflag
  have hz := StructuredCalls.embedState_register register stack frame
    (zeroState false false (CounterPrograms.isZero word) word) hregister 2
  have hform :
      (recordTrialResult register stack primeFlag frame word).regs primeFlag =
        ((StructuredCalls.embedState register stack frame
          (zeroState false false (CounterPrograms.isZero word) word)).regs primeFlag &&
        !(StructuredCalls.embedState register stack frame
          (zeroState false false (CounterPrograms.isZero word) word)).regs (register 2)) := by
    simp [recordTrialResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      BitProgram.execInstr, StructuredProgram.State.ofCfg, hne]
  rw [hform, hp, hz]
  rfl

/-- If the preceding actual remainder subroutine establishes its usual value
contract, this concrete accumulator records exactly nondivisibility. -/
theorem recordTrialResult_flag_nondivisor {R S : ℕ}
    (register : Fin 3 → Fin R) (stack : Fin 2 → Fin S)
    (hregister : Function.Injective register)
    (primeFlag : Fin R) (hflag : ¬ ∃ i, register i = primeFlag)
    (frame : StructuredProgram.State R S) (word : List Bool)
    (candidate divisor : ℕ)
    (hrem : BinaryArithmetic.toNat word = candidate % divisor) :
    (recordTrialResult register stack primeFlag frame word).regs primeFlag = true ↔
      frame.regs primeFlag = true ∧ candidate % divisor ≠ 0 := by
  rw [recordTrialResult_flag register stack hregister primeFlag hflag]
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  rw [CounterPrograms.isZero_eq_false_iff, CounterPrograms.value_eq_toNat, hrem]
  exact and_congr_right (fun _ => Nat.pos_iff_ne_zero)

/-- The verified accumulator has an actual primitive execution through the
proved compiler; this conclusion contains no assumed compilation certificate. -/
theorem recordTrial_primitive {R S : ℕ}
    (register : Fin 3 → Fin R) (stack : Fin 2 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (primeFlag : Fin R) (frame : StructuredProgram.State R S)
    (b p z : Bool) (word : List Bool) (inputStack outputStack : Fin S) :
    let c := recordTrial register stack primeFlag
    let prog := StructuredCalls.compiled c inputStack outputStack
    Computation.RunsIn (BitProgram.primitive prog).step
      (BitProgram.primitiveOverhead prog * (8 * word.length + 8 + 1))
      (BitProgram.primitiveCfg prog
        ((StructuredCalls.embedState register stack frame (zeroState b p z word)).withPC
          (some prog.entry)))
      (BitProgram.primitiveCfg prog
        ((recordTrialResult register stack primeFlag frame word).withPC none)) :=
  StructuredCalls.primitive_execution
    (recordTrial_eval register stack hregister hstack primeFlag frame b p z word)
    inputStack outputStack

private theorem extend_restrict_eq {A B C : Type*} (f : A → B) (g : B → C) :
    Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    exact Function.FactorsThrough.extend_apply (fun _ _ h => congrArg g h) g a
  · exact Function.extend_apply' _ _ _ h

private theorem state_ext {R S : ℕ} {a b : StructuredProgram.State R S}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

theorem zeroState_install_self {R S : ℕ}
    (register : Fin 3 → Fin R) (stack : Fin 2 → Fin S)
    (frame : StructuredProgram.State R S) (hs : frame.stacks (stack 1) = []) :
    StructuredCalls.embedState register stack frame
      (zeroState (frame.regs (register 0)) (frame.regs (register 1))
        (frame.regs (register 2)) (frame.stacks (stack 0))) = frame := by
  apply state_ext
  · change Function.extend register
      (CounterPrograms.counterRegs _ _ _) frame.regs = frame.regs
    have hr : CounterPrograms.counterRegs (frame.regs (register 0))
        (frame.regs (register 1)) (frame.regs (register 2)) = frame.regs ∘ register := by
      funext i
      fin_cases i <;> rfl
    rw [hr, extend_restrict_eq]
  · change Function.extend stack
      (CounterPrograms.counterStacks (frame.stacks (stack 0)) []) frame.stacks = frame.stacks
    have ht : CounterPrograms.counterStacks (frame.stacks (stack 0)) [] =
        frame.stacks ∘ stack := by
      funext i
      fin_cases i
      · rfl
      · exact hs.symm
    rw [ht, extend_restrict_eq]

theorem recordTrial_eval_state {R S : ℕ}
    (register : Fin 3 → Fin R) (stack : Fin 2 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (primeFlag : Fin R) (frame : StructuredProgram.State R S)
    (hs : frame.stacks (stack 1) = []) :
    StructuredCalls.Eval (recordTrial register stack primeFlag)
      (8 * (frame.stacks (stack 0)).length + 8) frame
      (recordTrialResult register stack primeFlag frame (frame.stacks (stack 0))) := by
  have h := recordTrial_eval register stack hregister hstack primeFlag frame
    (frame.regs (register 0)) (frame.regs (register 1)) (frame.regs (register 2))
    (frame.stacks (stack 0))
  rw [zeroState_install_self register stack frame hs] at h
  exact h

theorem recordTrialResult_stacks {R S : ℕ}
    (register : Fin 3 → Fin R) (stack : Fin 2 → Fin S)
    (primeFlag : Fin R) (frame : StructuredProgram.State R S)
    (hs : frame.stacks (stack 1) = []) :
    (recordTrialResult register stack primeFlag frame (frame.stacks (stack 0))).stacks =
      frame.stacks := by
  have h := congrArg StructuredProgram.State.stacks
    (zeroState_install_self register stack frame hs)
  simpa only [recordTrialResult, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, BitProgram.execInstr, StructuredProgram.State.withPC,
    StructuredProgram.State.ofCfg, StructuredCalls.embedState, zeroState] using h

/-- Division uses eight work registers; register eight is the caller's
primality accumulator and is outside the division program's register image. -/
def divisionRegister (i : Fin 8) : Fin 9 := i.castSucc

theorem divisionRegister_injective : Function.Injective divisionRegister := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 9 => x.val) h

def zeroRegister (i : Fin 3) : Fin 9 := ⟨i.val, by omega⟩
def zeroStack (i : Fin 2) : Fin 7 := ⟨i.val, by omega⟩

theorem zeroRegister_injective : Function.Injective zeroRegister := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 9 => x.val) h

theorem zeroStack_injective : Function.Injective zeroStack := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 7 => x.val) h

theorem flag_not_zeroRegister : ¬ ∃ i, zeroRegister i = (8 : Fin 9) := by
  rintro ⟨i, hi⟩
  have hv := congrArg (fun x : Fin 9 => x.val) hi
  change i.val = 8 at hv
  omega

def divisionFrame (flag : Bool) : StructuredProgram.State 9 7 :=
  ⟨fun _ => flag, fun _ => []⟩

noncomputable def divisionState (regs : Fin 8 → Bool) (flag : Bool)
    (result modulus input : List Bool) : StructuredProgram.State 9 7 :=
  StructuredCalls.embedState divisionRegister id (divisionFrame flag)
    ⟨regs, ModularDivisionPrograms.resting result modulus input⟩

@[simp] theorem divisionState_flag (regs : Fin 8 → Bool) (flag : Bool)
    (result modulus input : List Bool) :
    (divisionState regs flag result modulus input).regs 8 = flag := by
  apply StructuredCalls.embedState_register_frame
  rintro ⟨i, hi⟩
  have hv := congrArg (fun x : Fin 9 => x.val) hi
  change i.val = 8 at hv
  omega

@[simp] theorem divisionState_stacks (regs : Fin 8 → Bool) (flag : Bool)
    (result modulus input : List Bool) :
    (divisionState regs flag result modulus input).stacks =
      ModularDivisionPrograms.resting result modulus input := by
  simp [divisionState, StructuredCalls.embedState]

/-- A complete executable trial: binary remainder followed by the preserving
zero scan and update of the caller's primality accumulator. -/
abbrev divisibilityTrial : StructuredCalls.Cmd 9 7 :=
  .seq (.call (ProgramLinking.liftProgram ModularDivisionPrograms.remainderProgram
      divisionRegister id))
    (recordTrial zeroRegister zeroStack 8)

def divisibilityTrialBound (modulus input : List Bool) : ℕ :=
  100 * (modulus.length + input.length + 1) ^ 2 +
    8 * (modulus.length + input.length) + 8

/-- The program executes a genuine division on the supplied bit strings.
The modulus and input sizes are data, and all instruction tables remain fixed. -/
theorem divisibilityTrial_correct (regs : Fin 8 → Bool) (flag : Bool)
    (modulus input : List Bool) (hm : 0 < BinaryArithmetic.toNat modulus) :
    ∃ steps finalState,
      StructuredCalls.Eval divisibilityTrial steps
        (divisionState regs flag [] modulus input) finalState ∧
      steps ≤ divisibilityTrialBound modulus input ∧
      (finalState.regs 8 = true ↔
        flag = true ∧ BinaryArithmetic.toNat input % BinaryArithmetic.toNat modulus ≠ 0) ∧
      finalState.stacks =
        ModularDivisionPrograms.resting (ModularArithmetic.reduce modulus input) modulus [] := by
  obtain ⟨rf, t, ht, htrace⟩ := ModularDivisionPrograms.remainder_correct regs modulus input
  have htrace' : BitProgram.Trace ModularDivisionPrograms.remainderProgram t
      ((⟨regs, ModularDivisionPrograms.resting [] modulus input⟩ :
        StructuredProgram.State 8 7).withPC (some ModularDivisionPrograms.remainderProgram.entry))
      ((⟨rf, ModularDivisionPrograms.resting (ModularArithmetic.reduce modulus input) modulus []⟩ :
        StructuredProgram.State 8 7).withPC none) := htrace
  have hcall := StructuredCalls.eval_call_lifted
    ModularDivisionPrograms.remainderProgram divisionRegister id (divisionFrame flag)
    divisionRegister_injective Function.injective_id htrace'
  let middle := divisionState rf flag (ModularArithmetic.reduce modulus input) modulus []
  have hscratch : middle.stacks (zeroStack 1) = [] := by
    simp [middle, zeroStack, ModularDivisionPrograms.resting, ModularDivisionPrograms.seven]
  have hword : middle.stacks (zeroStack 0) = ModularArithmetic.reduce modulus input := by
    simp [middle, zeroStack, ModularDivisionPrograms.resting, ModularDivisionPrograms.seven]
  have hrecord := recordTrial_eval_state zeroRegister zeroStack zeroRegister_injective
    zeroStack_injective 8 middle hscratch
  rw [hword] at hrecord
  refine ⟨t + (8 * (ModularArithmetic.reduce modulus input).length + 8),
    recordTrialResult zeroRegister zeroStack 8 middle (ModularArithmetic.reduce modulus input),
    ?_, ?_, ?_, ?_⟩
  · exact hcall.seq hrecord
  · unfold divisibilityTrialBound
    rw [ModularArithmetic.reduce_length]
    omega
  · have hf := recordTrialResult_flag_nondivisor zeroRegister zeroStack
      zeroRegister_injective 8 flag_not_zeroRegister middle
      (ModularArithmetic.reduce modulus input) (BinaryArithmetic.toNat input)
      (BinaryArithmetic.toNat modulus) (ModularArithmetic.reduce_correct _ _ hm)
    simpa [middle] using hf
  · have hs := recordTrialResult_stacks zeroRegister zeroStack 8 middle hscratch
    rw [hword] at hs
    simpa [middle] using hs

/-- Total execution contract, including a zero-valued modulus.  The numeric
remainder interpretation requires a positive modulus, but finite execution does
not: it is established directly by the concrete binary reduction program. -/
theorem divisibilityTrial_execution (regs : Fin 8 → Bool) (flag : Bool)
    (modulus input : List Bool) :
    ∃ steps finalState,
      StructuredCalls.Eval divisibilityTrial steps
        (divisionState regs flag [] modulus input) finalState ∧
      steps ≤ divisibilityTrialBound modulus input ∧
      finalState.regs 8 =
        (flag && !(CounterPrograms.isZero (ModularArithmetic.reduce modulus input))) ∧
      finalState.stacks =
        ModularDivisionPrograms.resting (ModularArithmetic.reduce modulus input) modulus [] := by
  obtain ⟨rf, t, ht, htrace⟩ := ModularDivisionPrograms.remainder_correct regs modulus input
  have htrace' : BitProgram.Trace ModularDivisionPrograms.remainderProgram t
      ((⟨regs, ModularDivisionPrograms.resting [] modulus input⟩ :
        StructuredProgram.State 8 7).withPC (some ModularDivisionPrograms.remainderProgram.entry))
      ((⟨rf, ModularDivisionPrograms.resting (ModularArithmetic.reduce modulus input) modulus []⟩ :
        StructuredProgram.State 8 7).withPC none) := htrace
  have hcall := StructuredCalls.eval_call_lifted
    ModularDivisionPrograms.remainderProgram divisionRegister id (divisionFrame flag)
    divisionRegister_injective Function.injective_id htrace'
  let middle := divisionState rf flag (ModularArithmetic.reduce modulus input) modulus []
  have hscratch : middle.stacks (zeroStack 1) = [] := by
    simp [middle, zeroStack, ModularDivisionPrograms.resting, ModularDivisionPrograms.seven]
  have hword : middle.stacks (zeroStack 0) = ModularArithmetic.reduce modulus input := by
    simp [middle, zeroStack, ModularDivisionPrograms.resting, ModularDivisionPrograms.seven]
  have hrecord := recordTrial_eval_state zeroRegister zeroStack zeroRegister_injective
    zeroStack_injective 8 middle hscratch
  rw [hword] at hrecord
  refine ⟨t + (8 * (ModularArithmetic.reduce modulus input).length + 8),
    recordTrialResult zeroRegister zeroStack 8 middle (ModularArithmetic.reduce modulus input),
    hcall.seq hrecord, ?_, ?_, ?_⟩
  · unfold divisibilityTrialBound
    rw [ModularArithmetic.reduce_length]
    omega
  · simpa [middle] using recordTrialResult_flag zeroRegister zeroStack
      zeroRegister_injective 8 flag_not_zeroRegister middle
      (ModularArithmetic.reduce modulus input)
  · have hs := recordTrialResult_stacks zeroRegister zeroStack 8 middle hscratch
    rw [hword] at hs
    simpa [middle] using hs

end SubexponentialSAT.SubexpPrimeProgram

end OAI.Algorithms
