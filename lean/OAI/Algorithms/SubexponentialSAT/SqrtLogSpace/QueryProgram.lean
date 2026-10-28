import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import Mathlib.Tactic.FinCases

/-! Concrete bit primitives for streamed finite-difference queries. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

open OAI BitProgram
open scoped BigOperators

/-- Scan the actual bits, accumulating their XOR in register 2. -/
def parityProgram : Program 3 1 4 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 3, .bxor 2 2 0 0, .halt]

def parity : List Bool → Bool → Bool
  | [], b => b
  | bit :: bits, b => parity bits (Bool.xor b bit)

def parityStart (regs : Fin 3 → Bool) (bits : List Bool) : Cfg 3 1 4 :=
  ⟨some 0, regs, fun _ => bits⟩

def parityFinish (b : Bool) : Cfg 3 1 4 :=
  ⟨none, ![false, false, b], fun _ => []⟩

theorem parity_nil_trace (regs : Fin 3 → Bool) :
    Trace parityProgram 3 (parityStart regs []) (parityFinish (regs 2)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, parityProgram, parityStart, parityFinish,
    execInstr, readRegs]
  funext j
  fin_cases j <;> simp

theorem parity_cons_trace (regs : Fin 3 → Bool) (bit : Bool) (bits : List Bool) :
    Trace parityProgram 3 (parityStart regs (bit :: bits))
      (parityStart ![bit, true, Bool.xor (regs 2) bit] bits) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, parityProgram, parityStart, execInstr, readRegs]
  ext j
  fin_cases j <;> simp

theorem parity_program_trace (regs : Fin 3 → Bool) (bits : List Bool) :
    Trace parityProgram (3 * bits.length + 3) (parityStart regs bits)
      (parityFinish (parity bits (regs 2))) := by
  induction bits generalizing regs with
  | nil => exact parity_nil_trace regs
  | cons bit bits ih =>
      have h := (parity_cons_trace regs bit bits).trans
        (ih ![bit, true, Bool.xor (regs 2) bit])
      convert h using 1
      simp only [List.length_cons]
      omega
      congr 1

/-- The sign is determined by the number of true bits, not the length or
numeric value of the binary word. -/
theorem parity_sign {R : Type*} [Ring R] (bits : List Bool) (b : Bool) :
    (if parity bits b then (-1 : R) else 1) =
      (-1 : R) ^ bits.count true * (if b then -1 else 1) := by
  induction bits generalizing b with
  | nil => cases b <;> simp [parity]
  | cons bit bits ih =>
      rw [parity, ih]
      cases b <;> cases bit <;> simp [pow_succ]

/-- This scan is a polynomial-time local routine, so its complete local
prefix storage follows from the actual trace budget. -/
theorem parity_prefix_space (regs : Fin 3 → Bool) (bits : List Bool)
    (prefixSteps : ℕ) (c : Cfg 3 1 4) (hp : prefixSteps ≤ 3 * bits.length + 3)
    (htrace : Trace parityProgram prefixSteps (parityStart regs bits) c) :
    ∀ i, (c.stacks i).length ≤ dataBits (parityStart regs bits) + 3 * bits.length + 3 := by
  intro i
  have h := StructuredSpace.local_stack_bound parityProgram le_rfl prefixSteps c hp htrace i
  simpa [Nat.add_assoc] using h

open StructuredCalls

def scanCall {s : ℕ} (src : Fin s) : Cmd 3 s :=
  .call (ProgramLinking.liftProgram parityProgram id (fun _ => src))

def afterScan {s : ℕ} (d : State 3 s) (src : Fin s) : State 3 s :=
  ⟨![false, false, parity (d.stacks src) (d.regs 2)], Function.update d.stacks src []⟩

theorem scanCall_eval {s : ℕ} (d : State 3 s) (src : Fin s) :
    Eval (scanCall src) (3 * (d.stacks src).length + 3) d (afterScan d src) := by
  have hi : Function.Injective (fun _ : Fin 1 => src) := fun a b _ => Subsingleton.elim a b
  have h := eval_call_lifted parityProgram id (fun _ => src) d
    Function.injective_id hi
    (a := ⟨d.regs, fun _ => d.stacks src⟩)
    (b := ⟨![false, false, parity (d.stacks src) (d.regs 2)], fun _ => []⟩)
    (parity_program_trace d.regs (d.stacks src))
  have ha : embedState id (fun _ : Fin 1 => src) d
      ⟨d.regs, fun _ => d.stacks src⟩ = d := by
    apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id hi
    · intro i; rfl
    · intro i; rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j _; rfl
  have hb : embedState id (fun _ : Fin 1 => src) d
      ⟨![false, false, parity (d.stacks src) (d.regs 2)], fun _ => []⟩ =
        afterScan d src := by
    apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id hi
    · intro i; rfl
    · intro i; simp [afterScan]
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj
      have hj' : j ≠ src := fun h => hj ⟨0, h.symm⟩
      simp [afterScan, hj']
  change Eval (scanCall src) _ (embedState _ _ d _) (embedState _ _ d _) at h
  rwa [ha, hb] at h

/-- Finite table for the sign of a streamed pair. Both masks are preserved;
only one scan buffer and one copy temporary are needed. -/
def pairSign : Cmd 3 4 :=
  .seq (.base (.atom (.set 2 false)))
    (.seq (.call (StackRoutines.copyProgram 0 2 3 0 1))
      (.seq (scanCall 2)
        (.seq (.call (StackRoutines.copyProgram 1 2 3 0 1))
          (.seq (scanCall 2) (.base (.atom (.push 2 2)))))))

def pairStart (regs : Fin 3 → Bool) (E U : List Bool) : State 3 4 :=
  ⟨regs, ![E, U, [], []]⟩

def pairFinish (E U : List Bool) : State 3 4 :=
  ⟨![false, false, parity U (parity E false)],
    ![E, U, [parity U (parity E false)], []]⟩

theorem pairSign_eval (regs : Fin 3 → Bool) (E U : List Bool) :
    Eval pairSign (10 * (E.length + U.length) + 18)
      (pairStart regs E U) (pairFinish E U) := by
  let a₀ := pairStart regs E U
  let a₁ := StructuredProgram.Atom.eval (.set 2 false) a₀
  let a₂ := SubexpScanPrimitives.afterCopy a₁ 0 2 0 1
  let a₃ := afterScan a₂ 2
  let a₄ := SubexpScanPrimitives.afterCopy a₃ 1 2 0 1
  let a₅ := afterScan a₄ 2
  have h₀ : Eval (.base (.atom (.set 2 false))) 1 a₀ a₁ :=
    .base (.atom _ _)
  have h₁ := SubexpScanPrimitives.copy_eval a₁ 0 2 3 0 1
    (by decide) (by decide) (by decide) (by decide) (by rfl)
  have h₂ := scanCall_eval a₂ 2
  have h₃ := SubexpScanPrimitives.copy_eval a₃ 1 2 3 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [a₃, afterScan, a₂, SubexpScanPrimitives.afterCopy,
      StackRoutines.copyStacks, a₁, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, a₀,
      pairStart, StructuredProgram.State.ofCfg, execInstr])
  have h₄ := scanCall_eval a₄ 2
  have h₅ : Eval (.base (.atom (.push 2 2))) 1 a₅
      (StructuredProgram.Atom.eval (.push 2 2) a₅) := .base (.atom _ _)
  have h := h₀.seq (h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅))))
  have hs : StructuredProgram.Atom.eval (.push 2 2) a₅ = pairFinish E U := by
    apply SubexpScanPrimitives.state_ext
    · funext i
      fin_cases i <;>
        simp [a₅, afterScan, a₄, a₃, a₂, a₁, a₀, pairStart, pairFinish,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
          SubexpScanPrimitives.afterCopy,
          StackRoutines.copyStacks, execInstr, readRegs]
    · funext i
      fin_cases i <;>
        simp [a₅, afterScan, a₄, a₃, a₂, a₁, a₀, pairStart, pairFinish,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
          SubexpScanPrimitives.afterCopy,
          StackRoutines.copyStacks, execInstr, readRegs]
  rw [hs] at h
  convert h using 1
  · rfl
  · simp [afterScan, a₄, a₃, a₂, a₁, a₀, pairStart,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks, execInstr]
    omega

/-- Subset pairs have the finite-difference sign even though the machine only
computes XOR and never subtracts an unbounded integer. -/
theorem pairSign_correct {R : Type*} [Ring R] (E U : List Bool)
    (hU : U.count true ≤ E.count true) :
    (if parity U (parity E false) then (-1 : R) else 1) =
      (-1 : R) ^ (E.count true - U.count true) := by
  rw [parity_sign, parity_sign]
  simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
  rw [← pow_add]
  have h : U.count true + E.count true =
      E.count true - U.count true + 2 * U.count true := by omega
  rw [h, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

def pairSignProgram := compiled pairSign 0 2

theorem pairSign_trace (regs : Fin 3 → Bool) (E U : List Bool) :
    Trace pairSignProgram (10 * (E.length + U.length) + 19)
      ((pairStart regs E U).withPC (some pairSignProgram.entry))
      ((pairFinish E U).withPC none) := by
  simpa [pairSignProgram, Nat.add_assoc] using compiled_halt_trace (pairSign_eval regs E U) 0 2

/-- All prefixes of the fixed pair-sign program use polynomial local space.
This bound includes the preserved masks and both temporary stacks. -/
theorem pairSign_prefix_space (regs : Fin 3 → Bool) (E U : List Bool)
    (prefixSteps : ℕ) (c : Cfg 3 4 (StructuredCalls.size pairSign + 1))
    (hp : prefixSteps ≤ 10 * (E.length + U.length) + 19)
    (htrace : Trace pairSignProgram prefixSteps
      ((pairStart regs E U).withPC (some pairSignProgram.entry)) c) :
    ∀ i, (c.stacks i).length ≤ 11 * (E.length + U.length) + 19 := by
  intro i
  have hs : dataBits ((pairStart regs E U).withPC (some pairSignProgram.entry)) =
      E.length + U.length := by
    simp [dataBits, stackBits, pairStart, Fin.sum_univ_succ]
  have h := StructuredSpace.local_stack_bound pairSignProgram (le_of_eq hs)
    prefixSteps c hp htrace i
  omega

/-- Shared leaf ABI for pair signs: preserve both masks and every suspended
signature frame, with output848 and a single scratch word849. -/
def pairRegisters : Fin 3 → Fin 40 := Fin.castAdd 37

def pairStacks : Fin 4 → Fin 896 := ![834, 835, 848, 849]

theorem pairRegisters_injective : Function.Injective pairRegisters := Fin.castAdd_injective _ _

theorem pairStacks_injective : Function.Injective pairStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [pairStacks]

def pairSignCall : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram pairSignProgram pairRegisters pairStacks)

def pairCallResult (d : State 40 896) : State 40 896 :=
  let sign := parity (d.stacks 835) (parity (d.stacks 834) false)
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 sign,
    Function.update d.stacks 848 [sign]⟩

theorem pairSignCall_eval (d : State 40 896)
    (hout : d.stacks 848 = []) (htmp : d.stacks 849 = []) :
    Eval pairSignCall (10 * ((d.stacks 834).length + (d.stacks 835).length) + 19)
      d (pairCallResult d) := by
  let src := pairStart (fun i => d.regs (pairRegisters i)) (d.stacks 834) (d.stacks 835)
  let dst := pairFinish (d.stacks 834) (d.stacks 835)
  have hi : embedState pairRegisters pairStacks d src = d := by
    apply SubexpScanPrimitives.embedState_eq _ _ pairRegisters_injective pairStacks_injective
    · intro i; rfl
    · intro i
      fin_cases i <;> simp [src, pairStart, pairStacks, hout, htmp]
    · intro i _; rfl
    · intro i _; rfl
  have ho : embedState pairRegisters pairStacks d dst = pairCallResult d := by
    apply SubexpScanPrimitives.embedState_eq _ _ pairRegisters_injective pairStacks_injective
    · intro i
      fin_cases i <;> simp [dst, pairFinish, pairCallResult, pairRegisters]
    · intro i
      fin_cases i <;> simp [dst, pairFinish, pairCallResult, pairStacks, htmp]
    · intro i hi
      have h₀ : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h₁ : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      have h₂ : i ≠ 2 := fun h => hi ⟨2, h.symm⟩
      simp [pairCallResult, h₀, h₁, h₂]
    · intro i hi
      have h₈ : i ≠ 848 := fun h => hi ⟨2, h.symm⟩
      simp [pairCallResult, h₈]
  have h := eval_call_lifted pairSignProgram pairRegisters pairStacks d
    pairRegisters_injective pairStacks_injective
    (pairSign_trace (fun i => d.regs (pairRegisters i)) (d.stacks 834) (d.stacks 835))
  change Eval pairSignCall _ (embedState _ _ d src) (embedState _ _ d dst) at h
  rwa [hi, ho] at h

@[simp] theorem pairCallResult_stack_frame (d : State 40 896) (i : Fin 896)
    (hi : i ≠ 848) : (pairCallResult d).stacks i = d.stacks i := by
  simp [pairCallResult, hi]

section SignedArray

attribute [local simp] Fin.coe_ofNat_eq_mod

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

/-- The forty arithmetic ports are disjoint from the preserved sign bit. -/
def scalePorts : Fin 40 → Fin 41 := Fin.castAdd 1

theorem scalePorts_injective : Function.Injective scalePorts := Fin.castAdd_injective _ _

def signedState (regs : Fin 8 → Bool) (s : Squarefree.ScaleProgram.Store)
    (sign : Bool) : State 8 41 :=
  ⟨regs, fun i => if h : i.val < 40 then Squarefree.ScaleProgram.tapes s ⟨i.val, h⟩
    else [sign]⟩

theorem embed_signedState (regs rr : Fin 8 → Bool)
    (s t : Squarefree.ScaleProgram.Store) (sign : Bool) :
    embedState id scalePorts (signedState regs s sign) (Squarefree.ScaleProgram.state rr t) =
      signedState rr t sign := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id scalePorts_injective
  · intro i; rfl
  · intro i
    simp [signedState, scalePorts, Squarefree.ScaleProgram.state]
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi
    apply Fin.addCases (m := 40) (n := 1) (motive := fun i =>
      (¬ ∃ j, scalePorts j = i) →
        (signedState rr t sign).stacks i = (signedState regs s sign).stacks i) ?_ ?_ i hi
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j _; simp [signedState]

/-- A positive sign transfers unchanged bytes; a negative sign invokes the
original actual ternary scalar multiplier with its cached negative unit. -/
def signedScale : Cmd 8 41 :=
  .seq (.base (.atom (.peek 40 6 7)))
    (.ite 6 (.call (ProgramLinking.liftProgram Squarefree.ScaleProgram.program id scalePorts))
      (.seq (.call (StackRoutines.transferProgram 32 33 0 1))
        (.call (StackRoutines.transferProgram 33 38 0 1))))

def signedEntries (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d) (sign : Bool)
    (a : List (Product.Entry n (baseWidth p t) d)) :=
  if sign then Squarefree.ScaleProgram.scaled p t M cache table minusOne a else a

theorem signed_peek_eval (regs : Fin 8 → Bool) (s : Squarefree.ScaleProgram.Store)
    (sign : Bool) :
    Eval (.base (.atom (.peek 40 6 7))) 1 (signedState regs s sign)
      (signedState (readRegs regs 6 7 (some sign)) s sign) := by
  simpa [signedState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr]
    using (Eval.base (StructuredProgram.Eval.atom (.peek 40 6 7)
      (signedState regs s sign)))

theorem positiveScale_eval (regs : Fin 8 → Bool)
    (e : Squarefree.ScaleProgram.Environment) (bits : List Bool) :
    Eval (.seq (.call (StackRoutines.transferProgram 32 33 0 1))
      (.call (StackRoutines.transferProgram 33 38 0 1))) (6 * bits.length + 6)
      (signedState regs (Squarefree.ScaleProgram.idle e bits []) false)
      (signedState (readRegs (readRegs regs 0 1 none) 0 1 none)
        {Squarefree.ScaleProgram.idle e [] [] with output := bits} false) := by
  let a := signedState regs (Squarefree.ScaleProgram.idle e bits []) false
  let b := SubexpScanPrimitives.afterTransfer a 32 33 0 1
  have h₁ := SubexpScanPrimitives.transfer_eval a 32 33 0 1 (by decide) (by decide)
  have h₂ := SubexpScanPrimitives.transfer_eval b 33 38 0 1 (by decide) (by decide)
  have hb : SubexpScanPrimitives.afterTransfer b 33 38 0 1 =
      signedState (readRegs (readRegs regs 0 1 none) 0 1 none)
        {Squarefree.ScaleProgram.idle e [] [] with output := bits} false := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      have h32 : a.stacks 32 = bits := rfl
      have h33 : a.stacks 33 = [] := rfl
      have h38 : a.stacks 38 = [] := rfl
      simp only [b, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
        Function.update_apply, h32, h33, h38]
      by_cases hi32 : i = 32
      · subst i; simp [signedState, Squarefree.ScaleProgram.idle, Squarefree.ScaleProgram.tapes]
      by_cases hi33 : i = 33
      · subst i; simp [signedState, Squarefree.ScaleProgram.idle, Squarefree.ScaleProgram.tapes]
      by_cases hi38 : i = 38
      · subst i; simp [signedState, Squarefree.ScaleProgram.idle, Squarefree.ScaleProgram.tapes]
      simp only [hi32, hi33, hi38, ite_false]
      simp only [a, signedState]
      split_ifs with hi
      · simp only [Squarefree.ScaleProgram.tapes, Squarefree.ScaleProgram.idle]
        have hj32 : (⟨i.val, hi⟩ : Fin 40) ≠ 32 := by simpa [Fin.ext_iff] using hi32
        have hj38 : (⟨i.val, hi⟩ : Fin 40) ≠ 38 := by simpa [Fin.ext_iff] using hi38
        simp only [hj32, hj38, ite_false]
      · rfl
  have h := h₁.seq h₂
  rw [hb] at h
  have ha32 : a.stacks 32 = bits := rfl
  have hb33 : b.stacks 33 = bits.reverse := by
    simp [b, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, a,
      signedState, Squarefree.ScaleProgram.idle, Squarefree.ScaleProgram.tapes]
  simpa only [ha32, hb33, List.length_reverse, show
    3 * bits.length + 3 + (3 * bits.length + 3) = 6 * bits.length + 6 by omega] using h

def signedScalingBudget (n B d u J : ℕ) : ℕ :=
  TruncatedRingProgram.scalingBudget n B d u J +
    6 * (u * J * (2 * (u + J + n) + 2 * (d * B) + 2)) + 9

/-- The sign branch executes a fixed native program; readiness consists only
of the concrete scalar-ring data and bounded empty-support input dictionary. -/
theorem signedScale_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good ∅ u J a)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (regs : Fin 8 → Bool) (sign : Bool) :
    let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
    let result := signedEntries p t M cache table minusOne sign a
    ∃ steps rr, steps + 1 ≤ signedScalingBudget n (baseWidth p t) d u J ∧
      Eval signedScale steps
        (signedState regs (Squarefree.ScaleProgram.idle e (Product.bytes a) []) sign)
        (signedState rr {Squarefree.ScaleProgram.idle e [] [] with
          output := Product.bytes result} sign) ∧ Good ∅ u J result := by
  dsimp only
  let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
  have hp := signed_peek_eval regs (Squarefree.ScaleProgram.idle e (Product.bytes a) []) sign
  cases sign with
  | false =>
    have hh := positiveScale_eval (readRegs regs 6 7 (some false)) e (Product.bytes a)
    have he := hp.seq (Eval.ite_false (test := 6) (yes := .call (ProgramLinking.liftProgram Squarefree.ScaleProgram.program id scalePorts)) (by simp [signedState, readRegs]) hh)
    refine ⟨6 * (Product.bytes a).length + 8, readRegs (readRegs (readRegs regs 6 7 (some false)) 0 1 none) 0 1 none, ?_, ?_, ha⟩
    · have hb := TruncatedRingProgram.empty_bytes_length_le ha
      unfold signedScalingBudget
      omega
    · simpa only [signedScale, signedEntries, Bool.false_eq_true, ite_false, e, show 1 + (6 * (Product.bytes a).length + 6 + 1) = 6 * (Product.bytes a).length + 8 by omega] using he
  | true =>
    obtain ⟨steps, rr, hb, ht, hg, _⟩ := TruncatedRingProgram.scaling_run_space p t M cache hz
      table minusOne a ha degree width hd hw (readRegs regs 6 7 (some true))
    have hh := eval_call_lifted Squarefree.ScaleProgram.program id scalePorts
      (signedState (readRegs regs 6 7 (some true))
        (Squarefree.ScaleProgram.idle e (Product.bytes a) []) true)
      Function.injective_id scalePorts_injective ht
    rw [embed_signedState, embed_signedState] at hh
    have he := hp.seq (Eval.ite_true (test := 6) (no := .seq (.call (StackRoutines.transferProgram 32 33 0 1)) (.call (StackRoutines.transferProgram 33 38 0 1))) (by simp [signedState, readRegs]) hh)
    refine ⟨steps + 2, rr, ?_, ?_, hg⟩
    · unfold signedScalingBudget
      omega
    · simpa only [signedScale, signedEntries, Bool.true_eq, ite_true, e, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using he

def signedScaleProgram := compiled signedScale 32 38

theorem signedScale_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good ∅ u J a)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (regs : Fin 8 → Bool) (sign : Bool) :
    let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
    let start := (signedState regs (Squarefree.ScaleProgram.idle e (Product.bytes a) []) sign).withPC
      (some signedScaleProgram.entry)
    let result := signedEntries p t M cache table minusOne sign a
    ∃ steps rr, steps ≤ signedScalingBudget n (baseWidth p t) d u J ∧
      Trace signedScaleProgram steps start
        ((signedState rr {Squarefree.ScaleProgram.idle e [] [] with
          output := Product.bytes result} sign).withPC none) ∧ Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace signedScaleProgram prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          dataBits start + signedScalingBudget n (baseWidth p t) d u J := by
  dsimp only
  obtain ⟨steps, rr, hb, he, hg⟩ := signedScale_eval p t M cache hz table minusOne a ha
    degree width hd hw regs sign
  have ht := compiled_halt_trace he 32 38
  refine ⟨steps + 1, rr, hb, ht, hg, ?_⟩
  intro prefixSteps intermediate hp htrace
  exact StructuredSpace.local_stack_bound signedScaleProgram le_rfl prefixSteps intermediate
    (hp.trans hb) htrace


noncomputable section
variable {R : Type*} [CommRing R]

theorem signedEntries_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
    (sign : Bool) (a : List (Product.Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    TruncatedRingProgram.rawValue u J f (signedEntries p t M cache table minusOne sign a) =
      (if sign then -1 else 1) * TruncatedRingProgram.rawValue u J f a := by
  cases sign
  · simp [signedEntries]
  · simpa [signedEntries] using
      TruncatedRingProgram.negation_dense p t M cache scalar basis table htable u J minusOne hminus a

end

/-- Physical arithmetic registers lie below the four suspended DFS flags. -/
def leafArithmeticRegs : Fin 8 → Fin 40 := Fin.castAdd 32

theorem leafArithmeticRegs_injective : Function.Injective leafArithmeticRegs :=
  Fin.castAdd_injective _ _

/-- Consume the current pair array on 851; the sign remains on 848. -/
def leafScalePorts (i : Fin 41) : Fin 896 :=
  if i = 32 then 851 else if i = 40 then 848 else ⟨i.val, by omega⟩

theorem leafScalePorts_injective : Function.Injective leafScalePorts := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [leafScalePorts] at hv
  split_ifs at hv <;> simp_all [Fin.ext_iff] <;> omega

/-- Share the existing scalar parameters, consume scaled output 38, and
normalize into node accumulator 850. All other arithmetic scratch is below128. -/
def leafNormalizePorts (i : Fin 28) : Fin 896 :=
  if i = 5 then 5 else if i = 12 then 12 else if i = 24 then 39
  else if i = 15 then 850 else if i = 27 then 38 else ⟨100 + i.val, by omega⟩

theorem leafNormalizePorts_injective : Function.Injective leafNormalizePorts := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [leafNormalizePorts] at hv
  split_ifs at hv <;> simp_all [Fin.ext_iff] <;> omega

theorem leafScalePorts_not_acc : ¬ ∃ j, leafScalePorts j = 850 := by
  rintro ⟨j, hj⟩
  have h := congrArg Fin.val hj
  simp only [leafScalePorts] at h
  split_ifs at h <;> simp_all
  omega

theorem leafScalePorts_not_scratch (i : Fin 28) :
    ¬ ∃ j, leafScalePorts j = (⟨100 + i.val, by omega⟩ : Fin 896) := by
  rintro ⟨j, hj⟩
  have h := congrArg Fin.val hj
  simp only [leafScalePorts] at h
  split_ifs at h <;> simp_all <;> omega

/-- One actual signed finite-difference term is added to the retained node
array. Neither call constructs a support family or an assignment product. -/
def signedAccumulate : Cmd 40 896 :=
  .seq (.call (ProgramLinking.liftProgram signedScaleProgram leafArithmeticRegs leafScalePorts))
    (.call (ProgramLinking.liftProgram Normalize.program leafArithmeticRegs leafNormalizePorts))

def signedAccumulateProgram := compiled signedAccumulate 851 850

def signedAccumulateBudget (n B d u J : ℕ) : ℕ :=
  signedScalingBudget n B d u J + TruncatedRingProgram.additionBudget n B d u J + 1

/-- Concrete port readiness for the signed scaler. This is a physical input
condition for this local instruction sequence, not an evaluation service. -/
structure ScaleReady (d : State 40 896) (e : Squarefree.ScaleProgram.Environment)
    (source : List Bool) (sign : Bool) : Prop where
  «stacks» : ∀ i, d.stacks (leafScalePorts i) =
    (signedState (fun j => d.regs (leafArithmeticRegs j))
      (Squarefree.ScaleProgram.idle e source []) sign).stacks i

/-- Only the normalizer's peripheral scratch must be empty. Its parameters
are shared with the actual scalar machine. -/
structure NormalizeScratchReady (d : State 40 896) : Prop where
  empty : ∀ i : Fin 28, i ≠ 5 → i ≠ 12 → i ≠ 24 → i ≠ 15 → i ≠ 27 →
    d.stacks (leafNormalizePorts i) = []

theorem embed_scale_ready (d : State 40 896) (e : Squarefree.ScaleProgram.Environment)
    (source : List Bool) (sign : Bool) (h : ScaleReady d e source sign) :
    embedState leafArithmeticRegs leafScalePorts d
      (signedState (fun j => d.regs (leafArithmeticRegs j))
        (Squarefree.ScaleProgram.idle e source []) sign) = d := by
  apply SubexpScanPrimitives.embedState_eq _ _ leafArithmeticRegs_injective
    leafScalePorts_injective
  · intro i; rfl
  · exact h.stacks
  · intros; rfl
  · intros; rfl

theorem normalize_after_scale (d : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr : Fin 8 → Bool)
    (source seed : List Bool) (sign : Bool) (hs : NormalizeScratchReady d)
    (ha : d.stacks 850 = seed) :
    let mid := embedState leafArithmeticRegs leafScalePorts d
      (signedState rr {Squarefree.ScaleProgram.idle e [] [] with output := source} sign)
    embedState leafArithmeticRegs leafNormalizePorts mid
      (Normalize.state rr e.modulus e.width e.count seed source) = mid := by
  dsimp only
  let mid := embedState leafArithmeticRegs leafScalePorts d
    (signedState rr {Squarefree.ScaleProgram.idle e [] [] with output := source} sign)
  apply SubexpScanPrimitives.embedState_eq _ _ leafArithmeticRegs_injective
    leafNormalizePorts_injective
  · intro i
    exact embedState_register _ _ _ _ leafArithmeticRegs_injective i
  · intro i
    by_cases h5 : i = 5
    · subst i
      change mid.stacks (leafScalePorts 5) = e.modulus
      rw [embedState_stack _ _ _ _ leafScalePorts_injective]
      rfl
    by_cases h12 : i = 12
    · subst i
      change mid.stacks (leafScalePorts 12) = e.width
      rw [embedState_stack _ _ _ _ leafScalePorts_injective]
      rfl
    by_cases h24 : i = 24
    · subst i
      change mid.stacks (leafScalePorts 39) = e.count
      rw [embedState_stack _ _ _ _ leafScalePorts_injective]
      rfl
    by_cases h15 : i = 15
    · subst i
      change mid.stacks 850 = seed
      rw [embedState_stack_frame _ _ _ _ _ leafScalePorts_not_acc]
      exact ha
    by_cases h27 : i = 27
    · subst i
      change mid.stacks (leafScalePorts 38) = source
      rw [embedState_stack _ _ _ _ leafScalePorts_injective]
      rfl
    have hh : (Normalize.state rr e.modulus e.width e.count seed source).stacks i = [] := by
      have hn5 : i.val ≠ 5 := by simpa [Fin.ext_iff] using h5
      have hn12 : i.val ≠ 12 := by simpa [Fin.ext_iff] using h12
      have hn24 : i.val ≠ 24 := by simpa [Fin.ext_iff] using h24
      have hn15 : i.val ≠ 15 := by simpa [Fin.ext_iff] using h15
      have hn27 : i.val ≠ 27 := by simpa [Fin.ext_iff] using h27
      have hi : i.val < 27 := by omega
      change Fin.snoc (α := fun _ : Fin 28 => List Bool) (Dictionary.tapes (Dictionary.outputTape
        e.modulus e.width e.count seed [])) source i = []
      rw [show i = (⟨i.val, hi⟩ : Fin 27).castSucc from rfl, Fin.snoc_castSucc]
      have hj5 : (⟨i.val, hi⟩ : Fin 27) ≠ 5 := fun h => hn5 (congrArg Fin.val h)
      have hj12 : (⟨i.val, hi⟩ : Fin 27) ≠ 12 := fun h => hn12 (congrArg Fin.val h)
      have hj24 : (⟨i.val, hi⟩ : Fin 27) ≠ 24 := fun h => hn24 (congrArg Fin.val h)
      have hj15 : (⟨i.val, hi⟩ : Fin 27) ≠ 15 := fun h => hn15 (congrArg Fin.val h)
      simp only [Dictionary.outputTape, Dictionary.tapes, hj5, hj12, hj24, hj15,
        ite_false, ite_self]
    rw [hh]
    have hp : leafNormalizePorts i = ⟨100 + i.val, by omega⟩ := by
      simp [leafNormalizePorts, h5, h12, h24, h15, h27]
    rw [hp, embedState_stack_frame _ _ _ _ _ (leafScalePorts_not_scratch i)]
    simpa only [hp] using hs.empty i h5 h12 h24 h15 h27
  · intros; rfl
  · intros; rfl

/-- The normalized result is an exact signed addition in the retained array. -/
def signedSum (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d) (sign : Bool)
    (source seed : List (Product.Entry n (baseWidth p t) d)) :=
  Normalize.run p t M cache (signedEntries p t M cache table minusOne sign source) seed

noncomputable def scaleLeafResult (d : State 40 896) (e : Squarefree.ScaleProgram.Environment)
    (rr : Fin 8 → Bool) (source : List Bool) (sign : Bool) : State 40 896 :=
  embedState leafArithmeticRegs leafScalePorts d
    (signedState rr {Squarefree.ScaleProgram.idle e [] [] with output := source} sign)

noncomputable def accumulateLeafResult (d : State 40 896) (e : Squarefree.ScaleProgram.Environment)
    (rr ss : Fin 8 → Bool) (source result : List Bool) (sign : Bool) : State 40 896 :=
  embedState leafArithmeticRegs leafNormalizePorts (scaleLeafResult d e rr source sign)
    (Normalize.state ss e.modulus e.width e.count result [])

/-- Both arithmetic branches and the additive normalization execute on one
fixed physical command. The initial hypotheses describe its actual input words. -/
theorem signedAccumulate_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d) (sign : Bool)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (caller : State 40 896)
    (hscale : ScaleReady caller (Squarefree.ScaleProgram.environment p t M cache table
      minusOne degree width) (Product.bytes source) sign)
    (hscratch : NormalizeScratchReady caller) (hacc : caller.stacks 850 = Product.bytes seed) :
    let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
    let scaled := signedEntries p t M cache table minusOne sign source
    let result := signedSum p t M cache table minusOne sign source seed
    ∃ steps rr ss,
      steps + 1 ≤ signedAccumulateBudget n (baseWidth p t) d u J ∧
      Eval signedAccumulate steps caller
        (accumulateLeafResult caller e rr ss (Product.bytes scaled) (Product.bytes result) sign) ∧
      Good ∅ u J result := by
  dsimp only
  let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
  let scaled := signedEntries p t M cache table minusOne sign source
  obtain ⟨st, rr, hb, ht, hg, _⟩ := signedScale_run_space p t M cache hz table minusOne
    source hsource degree width hd hw (fun i => caller.regs (leafArithmeticRegs i)) sign
  have he := eval_call_lifted signedScaleProgram leafArithmeticRegs leafScalePorts caller
    leafArithmeticRegs_injective leafScalePorts_injective ht
  rw [embed_scale_ready caller e (Product.bytes source) sign hscale] at he
  let mid := scaleLeafResult caller e rr (Product.bytes scaled) sign
  change Eval _ st caller mid at he
  obtain ⟨atime, ss, hab, hat, hag, _⟩ := TruncatedRingProgram.addition_run_space
    p t M cache scaled seed hg hseed rr width degree hd hw
  have hae := eval_call_lifted Normalize.program leafArithmeticRegs leafNormalizePorts mid
    leafArithmeticRegs_injective leafNormalizePorts_injective hat
  have hi : embedState leafArithmeticRegs leafNormalizePorts mid
      (Normalize.state rr M.bits width degree (Product.bytes seed) (Product.bytes scaled)) = mid :=
    normalize_after_scale caller e rr (Product.bytes scaled) (Product.bytes seed) sign
      hscratch hacc
  rw [hi] at hae
  refine ⟨st + atime, rr, ss, ?_, ?_, hag⟩
  · unfold signedAccumulateBudget
    omega
  · exact he.seq hae

/-- The compiled signed addition has a polynomial bound at every local source
prefix, measured from all caller stacks, including persistent query state. -/
theorem signedAccumulate_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d) (sign : Bool)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (caller : State 40 896)
    (hscale : ScaleReady caller (Squarefree.ScaleProgram.environment p t M cache table
      minusOne degree width) (Product.bytes source) sign)
    (hscratch : NormalizeScratchReady caller) (hacc : caller.stacks 850 = Product.bytes seed) :
    let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
    let scaled := signedEntries p t M cache table minusOne sign source
    let result := signedSum p t M cache table minusOne sign source seed
    let start := caller.withPC (some signedAccumulateProgram.entry)
    ∃ steps rr ss,
      steps ≤ signedAccumulateBudget n (baseWidth p t) d u J ∧
      Trace signedAccumulateProgram steps start
        ((accumulateLeafResult caller e rr ss (Product.bytes scaled) (Product.bytes result)
          sign).withPC none) ∧ Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace signedAccumulateProgram prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          dataBits start + signedAccumulateBudget n (baseWidth p t) d u J := by
  dsimp only
  obtain ⟨steps, rr, ss, hb, he, hg⟩ := signedAccumulate_eval p t M cache hz table minusOne
    sign source seed hsource hseed degree width hd hw caller hscale hscratch hacc
  refine ⟨steps + 1, rr, ss, hb, compiled_halt_trace he 851 850, hg, ?_⟩
  intro prefixSteps intermediate hp ht
  exact StructuredSpace.local_stack_bound signedAccumulateProgram le_rfl prefixSteps intermediate
    (hp.trans hb) ht

noncomputable section
variable {R : Type*} [CommRing R]

theorem signedSum_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
    (sign : Bool) (source seed : List (Product.Entry n (baseWidth p t) d))
    (hseed : (Squarefree.Sparse.keys seed).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    TruncatedRingProgram.rawValue u J f (signedSum p t M cache table minusOne sign source seed) =
      (if sign then -1 else 1) * TruncatedRingProgram.rawValue u J f source +
        TruncatedRingProgram.rawValue u J f seed := by
  dsimp only [signedSum]
  rw [TruncatedRingProgram.normalize_dense p t M cache scalar basis u J _ seed hseed,
    signedEntries_dense p t M cache scalar basis table htable u J minusOne hminus sign source]

end

theorem signedState_unchanged (regs rr : Fin 8 → Bool)
    (e : Squarefree.ScaleProgram.Environment) (source output : List Bool) (sign : Bool)
    (i : Fin 41) (h32 : i ≠ 32) (h38 : i ≠ 38) :
    (signedState rr {Squarefree.ScaleProgram.idle e [] [] with output := output} sign).stacks i =
      (signedState regs (Squarefree.ScaleProgram.idle e source []) sign).stacks i := by
  simp only [signedState]
  split_ifs with hi
  · have hj32 : (⟨i.val, hi⟩ : Fin 40) ≠ 32 := by simpa [Fin.ext_iff] using h32
    have hj38 : (⟨i.val, hi⟩ : Fin 40) ≠ 38 := by simpa [Fin.ext_iff] using h38
    simp only [Squarefree.ScaleProgram.tapes, Squarefree.ScaleProgram.idle,
      hj32, hj38, ite_false]
  · rfl

theorem scaleLeafResult_frame (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr : Fin 8 → Bool)
    (source output : List Bool) (sign : Bool) (h : ScaleReady caller e source sign)
    (i : Fin 896) (h38 : i ≠ 38) (h851 : i ≠ 851) :
    (scaleLeafResult caller e rr output sign).stacks i = caller.stacks i := by
  by_cases hi : ∃ j, leafScalePorts j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [scaleLeafResult, embedState_stack _ _ _ _ leafScalePorts_injective, h.stacks j]
    apply signedState_unchanged
    · intro he; subst j; exact h851 rfl
    · intro he; subst j; exact h38 rfl
  · exact embedState_stack_frame _ _ _ _ _ hi

theorem normalizeState_unchanged (regs rr : Fin 8 → Bool)
    (modulus width degree source seed result : List Bool)
    (i : Fin 28) (h15 : i ≠ 15) (h27 : i ≠ 27) :
    (Normalize.state rr modulus width degree result []).stacks i =
      (Normalize.state regs modulus width degree seed source).stacks i := by
  have hn27 : i.val ≠ 27 := by simpa [Fin.ext_iff] using h27
  have hi : i.val < 27 := by omega
  change Fin.snoc (α := fun _ : Fin 28 => List Bool)
    (Dictionary.tapes (Dictionary.outputTape modulus width degree result [])) [] i =
      Fin.snoc (α := fun _ : Fin 28 => List Bool)
        (Dictionary.tapes (Dictionary.outputTape modulus width degree seed [])) source i
  rw [show i = (⟨i.val, hi⟩ : Fin 27).castSucc from rfl,
    Fin.snoc_castSucc, Fin.snoc_castSucc]
  have hj15 : (⟨i.val, hi⟩ : Fin 27) ≠ 15 := by simpa [Fin.ext_iff] using h15
  simp only [Dictionary.tapes, Dictionary.outputTape, hj15, ite_false]

theorem accumulateLeafResult_normalize_frame (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (source seed result : List Bool) (sign : Bool)
    (hs : NormalizeScratchReady caller) (ha : caller.stacks 850 = seed)
    (i : Fin 896) (h850 : i ≠ 850) (h38 : i ≠ 38) :
    (accumulateLeafResult caller e rr ss source result sign).stacks i =
      (scaleLeafResult caller e rr source sign).stacks i := by
  by_cases hi : ∃ j, leafNormalizePorts j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [accumulateLeafResult, embedState_stack _ _ _ _ leafNormalizePorts_injective]
    have hready := normalize_after_scale caller e rr source seed sign hs ha
    have he := congrArg (fun d : State 40 896 => d.stacks (leafNormalizePorts j)) hready
    dsimp only at he
    rw [embedState_stack _ _ _ _ leafNormalizePorts_injective] at he
    change (Normalize.state rr e.modulus e.width e.count seed source).stacks j =
      (scaleLeafResult caller e rr source sign).stacks (leafNormalizePorts j) at he
    rw [← he]
    apply normalizeState_unchanged
    · intro hh; subst j; exact h850 rfl
    · intro hh; subst j; exact h38 rfl
  · exact embedState_stack_frame _ _ _ _ _ hi

@[simp] theorem accumulateLeafResult_accumulator (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (source result : List Bool) (sign : Bool) :
    (accumulateLeafResult caller e rr ss source result sign).stacks 850 = result := by
  change (accumulateLeafResult caller e rr ss source result sign).stacks (leafNormalizePorts 15) = _
  rw [accumulateLeafResult, embedState_stack _ _ _ _ leafNormalizePorts_injective]
  rfl

@[simp] theorem accumulateLeafResult_source (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (source result : List Bool) (sign : Bool) :
    (accumulateLeafResult caller e rr ss source result sign).stacks 38 = [] := by
  change (accumulateLeafResult caller e rr ss source result sign).stacks (leafNormalizePorts 27) = _
  rw [accumulateLeafResult, embedState_stack _ _ _ _ leafNormalizePorts_injective]
  rfl

theorem accumulateLeafResult_frame (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (input source seed result : List Bool) (sign : Bool)
    (hscale : ScaleReady caller e input sign)
    (hs : NormalizeScratchReady caller) (ha : caller.stacks 850 = seed)
    (i : Fin 896) (h850 : i ≠ 850) (h851 : i ≠ 851) :
    (accumulateLeafResult caller e rr ss source result sign).stacks i = caller.stacks i := by
  by_cases h38 : i = 38
  · subst i
    rw [accumulateLeafResult_source]
    exact (hscale.stacks 38).symm
  · rw [accumulateLeafResult_normalize_frame caller e rr ss source seed result sign hs ha i h850 h38]
    exact scaleLeafResult_frame caller e rr input source sign hscale i h38 h851

@[simp] theorem accumulateLeafResult_consumed (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (source seed result : List Bool) (sign : Bool)
    (hs : NormalizeScratchReady caller) (ha : caller.stacks 850 = seed) :
    (accumulateLeafResult caller e rr ss source result sign).stacks 851 = [] := by
  rw [accumulateLeafResult_normalize_frame caller e rr ss source seed result sign hs ha
    851 (by decide) (by decide)]
  change (scaleLeafResult caller e rr source sign).stacks (leafScalePorts 32) = _
  rw [scaleLeafResult, embedState_stack _ _ _ _ leafScalePorts_injective]
  rfl

theorem pairCallResult_scaleReady (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (input : List Bool)
    (h : ∀ i : Fin 40, caller.stacks (leafScalePorts (Fin.castAdd 1 i)) =
      Squarefree.ScaleProgram.tapes (Squarefree.ScaleProgram.idle e input []) i) :
    ScaleReady (pairCallResult caller) e input
      (parity (caller.stacks 835) (parity (caller.stacks 834) false)) := by
  constructor
  intro i
  induction i using (Fin.addCases (m := 40) (n := 1)) with
  | left i =>
    have hne : leafScalePorts (Fin.castAdd 1 i) ≠ 848 := by
      intro he
      have hh := leafScalePorts_injective (show leafScalePorts (Fin.castAdd 1 i) =
        leafScalePorts 40 from he)
      have hv := congrArg Fin.val hh
      change i.val = 40 at hv
      omega
    rw [pairCallResult_stack_frame _ _ hne, h i]
    simp [signedState]
  | right i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl

theorem pairCallResult_normalizeScratch (caller : State 40 896)
    (h : NormalizeScratchReady caller) : NormalizeScratchReady (pairCallResult caller) := by
  constructor
  intro i h5 h12 h24 h15 h27
  have hn : leafNormalizePorts i ≠ 848 := by
    simp [leafNormalizePorts, h5, h12, h24, h15, h27, Fin.ext_iff]
    omega
  rw [pairCallResult_stack_frame _ _ hn]
  exact h.empty i h5 h12 h24 h15 h27

/-- Update the node accumulator for a completed pair and clear its sign cell
before the next pair. The pair masks themselves are read and restored. -/
def pairUpdate : Cmd 40 896 :=
  .seq pairSignCall (.seq signedAccumulate (.base (.atom (.pop 848 0 1))))

def pairUpdateProgram := compiled pairUpdate 851 850

noncomputable def pairUpdateResult (d : State 40 896) : State 40 896 :=
  ⟨readRegs d.regs 0 1 (d.stacks 848).head?, Function.update d.stacks 848 []⟩

def pairUpdateBudget (n B d u J E U : ℕ) : ℕ :=
  10 * (E + U) + signedAccumulateBudget n B d u J + 20

/-- Exact actual signed update, including mask scans and sign cleanup. -/
theorem pairUpdate_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (caller : State 40 896)
    (hlow : ∀ i : Fin 40, caller.stacks (leafScalePorts (Fin.castAdd 1 i)) =
      Squarefree.ScaleProgram.tapes (Squarefree.ScaleProgram.idle
        (Squarefree.ScaleProgram.environment p t M cache table minusOne degree width)
        (Product.bytes source) []) i)
    (hscratch : NormalizeScratchReady caller) (hacc : caller.stacks 850 = Product.bytes seed)
    (hsign : caller.stacks 848 = []) (htmp : caller.stacks 849 = []) :
    let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
    let sign := parity (caller.stacks 835) (parity (caller.stacks 834) false)
    let scaled := signedEntries p t M cache table minusOne sign source
    let result := signedSum p t M cache table minusOne sign source seed
    ∃ steps rr ss,
      steps + 1 ≤ pairUpdateBudget n (baseWidth p t) d u J
        (caller.stacks 834).length (caller.stacks 835).length ∧
      Eval pairUpdate steps caller
        (pairUpdateResult (accumulateLeafResult (pairCallResult caller) e rr ss
          (Product.bytes scaled) (Product.bytes result) sign)) ∧ Good ∅ u J result := by
  dsimp only
  let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
  let sign := parity (caller.stacks 835) (parity (caller.stacks 834) false)
  let scaled := signedEntries p t M cache table minusOne sign source
  let result := signedSum p t M cache table minusOne sign source seed
  have hs := pairCallResult_scaleReady caller e (Product.bytes source) hlow
  have hsc := pairCallResult_normalizeScratch caller hscratch
  have ha : (pairCallResult caller).stacks 850 = Product.bytes seed := by
    rw [pairCallResult_stack_frame _ _ (by decide)]
    exact hacc
  obtain ⟨steps, rr, ss, hb, he, hg⟩ := signedAccumulate_eval p t M cache hz table minusOne
    sign source seed hsource hseed degree width hd hw (pairCallResult caller) hs hsc ha
  let out := accumulateLeafResult (pairCallResult caller) e rr ss
    (Product.bytes scaled) (Product.bytes result) sign
  have ho : out.stacks 848 = [sign] := by
    rw [accumulateLeafResult_frame (pairCallResult caller) e rr ss (Product.bytes source)
      (Product.bytes scaled) (Product.bytes seed) (Product.bytes result) sign hs hsc ha
      848 (by decide) (by decide)]
    rfl
  have hp : Eval (.base (.atom (.pop 848 0 1))) 1 out (pairUpdateResult out) := by
    convert Eval.base (StructuredProgram.Eval.atom (.pop 848 0 1) out) using 1
    apply SubexpScanPrimitives.state_ext
    · rfl
    · change Function.update out.stacks 848 [] =
        Function.update out.stacks 848 (out.stacks 848).tail
      rw [ho]
      rfl
  refine ⟨10 * ((caller.stacks 834).length + (caller.stacks 835).length) + 19 + (steps + 1),
    rr, ss, ?_, (pairSignCall_eval caller hsign htmp).seq (he.seq hp), hg⟩
  unfold pairUpdateBudget
  omega

/-- The mask scan, signed update and cleanup share this same compiled run. -/
theorem pairUpdate_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (caller : State 40 896)
    (hlow : ∀ i : Fin 40, caller.stacks (leafScalePorts (Fin.castAdd 1 i)) =
      Squarefree.ScaleProgram.tapes (Squarefree.ScaleProgram.idle
        (Squarefree.ScaleProgram.environment p t M cache table minusOne degree width)
        (Product.bytes source) []) i)
    (hscratch : NormalizeScratchReady caller) (hacc : caller.stacks 850 = Product.bytes seed)
    (hsign : caller.stacks 848 = []) (htmp : caller.stacks 849 = []) :
    let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
    let sign := parity (caller.stacks 835) (parity (caller.stacks 834) false)
    let scaled := signedEntries p t M cache table minusOne sign source
    let result := signedSum p t M cache table minusOne sign source seed
    let start := caller.withPC (some pairUpdateProgram.entry)
    ∃ steps rr ss,
      steps ≤ pairUpdateBudget n (baseWidth p t) d u J
        (caller.stacks 834).length (caller.stacks 835).length ∧
      Trace pairUpdateProgram steps start
        ((pairUpdateResult (accumulateLeafResult (pairCallResult caller) e rr ss
          (Product.bytes scaled) (Product.bytes result) sign)).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace pairUpdateProgram prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤ dataBits start +
          pairUpdateBudget n (baseWidth p t) d u J
            (caller.stacks 834).length (caller.stacks 835).length := by
  dsimp only
  obtain ⟨steps, rr, ss, hb, he, hg⟩ := pairUpdate_eval p t M cache hz table minusOne source seed
    hsource hseed degree width hd hw caller hlow hscratch hacc hsign htmp
  refine ⟨steps + 1, rr, ss, hb, compiled_halt_trace he 851 850, hg, ?_⟩
  intro prefixSteps intermediate hp ht
  exact StructuredSpace.local_stack_bound pairUpdateProgram le_rfl prefixSteps intermediate
    (hp.trans hb) ht

/-- Exact stack framing of the complete pair arithmetic: only node850 and
consumed pair851 differ from the input state. In particular E/U, all suspended
representatives, and every loader/cache master survive. -/
theorem pairUpdateResult_frame (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (input source seed result : List Bool)
    (hlow : ∀ i : Fin 40, caller.stacks (leafScalePorts (Fin.castAdd 1 i)) =
      Squarefree.ScaleProgram.tapes (Squarefree.ScaleProgram.idle e input []) i)
    (hs : NormalizeScratchReady caller) (ha : caller.stacks 850 = seed)
    (hsign : caller.stacks 848 = [])
    (i : Fin 896) (h850 : i ≠ 850) (h851 : i ≠ 851) :
    let sign := parity (caller.stacks 835) (parity (caller.stacks 834) false)
    (pairUpdateResult (accumulateLeafResult (pairCallResult caller) e rr ss source result sign)).stacks i =
      caller.stacks i := by
  dsimp only
  by_cases hi : i = 848
  · subst i
    simp [pairUpdateResult, hsign]
  · simp only [pairUpdateResult, Function.update_of_ne hi]
    have hscale := pairCallResult_scaleReady caller e input hlow
    have hscratch := pairCallResult_normalizeScratch caller hs
    have hacc : (pairCallResult caller).stacks 850 = seed := by
      rw [pairCallResult_stack_frame _ _ (by decide)]
      exact ha
    rw [accumulateLeafResult_frame (pairCallResult caller) e rr ss input source seed result
      _ hscale hscratch hacc i h850 h851, pairCallResult_stack_frame _ _ hi]

@[simp] theorem pairUpdateResult_accumulator (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (source result : List Bool) (sign : Bool) :
    (pairUpdateResult (accumulateLeafResult caller e rr ss source result sign)).stacks 850 = result := by
  simp [pairUpdateResult]

noncomputable section
variable {R : Type*} [CommRing R]

/-- The actual Boolean parity used by the program is the exact
finite-difference sign, including the empty support. -/
theorem pair_signedSum_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
    (E U : List Bool) (hU : U.count true ≤ E.count true)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hseed : (Squarefree.Sparse.keys seed).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    TruncatedRingProgram.rawValue u J f
      (signedSum p t M cache table minusOne (parity U (parity E false)) source seed) =
        (-1 : Dense R u J) ^ (E.count true - U.count true) *
          TruncatedRingProgram.rawValue u J f source + TruncatedRingProgram.rawValue u J f seed := by
  dsimp only
  rw [signedSum_dense p t M cache scalar basis table htable u J minusOne hminus _ source seed hseed,
    pairSign_correct E U hU]

end

end SignedArray

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
