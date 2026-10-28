import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Algorithm
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# Remaining-budget successor for bounded exponent vectors

Coordinates are stored in reverse order, with the fastest-changing coordinate
first.  A coordinate `a` is the word `false :: replicate a true`.  This is the
reverse of the usual forward unary-delimited exponent encoding.  A separate
unary stack records the unused total-degree budget.
-/

namespace SubexponentialSAT.SubexpExponentSuccessor

open SubexponentialSAT.BitProgram

def digitsCode (digits : List ℕ) : List Bool :=
  digits.flatMap fun a => false :: List.replicate a true

@[simp] theorem digitsCode_nil : digitsCode [] = [] := rfl

@[simp] theorem digitsCode_cons (a : ℕ) (digits : List ℕ) :
    digitsCode (a :: digits) =
      false :: (List.replicate a true ++ digitsCode digits) := by
  simp [digitsCode]

theorem digitsCode_append (as bs : List ℕ) :
    digitsCode (as ++ bs) = digitsCode as ++ digitsCode bs := by
  simp [digitsCode]

theorem digitsCode_reverse_unary (digits : List ℕ) :
    digitsCode digits = (SymbolicCost.unaryWords digits.reverse).reverse := by
  induction digits with
  | nil => rfl
  | cons a digits ih =>
    simp [digitsCode_cons, SymbolicCost.unaryWords, SymbolicCost.unaryWord,
      List.flatMap_append, ih]

@[simp] theorem digitsCode_zeroes (n : ℕ) :
    digitsCode (List.replicate n 0) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- Increment the fastest coordinate when budget remains.  Otherwise reset
it, restore its budget, and carry to the next coordinate. -/
def nextDigits : List ℕ → ℕ → Option (List ℕ × ℕ)
  | [], _ => none
  | a :: digits, budget + 1 => some ((a + 1) :: digits, budget)
  | a :: digits, 0 => (nextDigits digits a).map fun next => (0 :: next.1, next.2)

theorem nextDigits_length {digits next : List ℕ} {budget remaining : ℕ}
    (h : nextDigits digits budget = some (next, remaining)) :
    next.length = digits.length := by
  induction digits generalizing next budget remaining with
  | nil => simp [nextDigits] at h
  | cons a digits ih =>
    cases budget with
    | succ budget =>
      simp only [nextDigits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | zero =>
      cases hn : nextDigits digits a with
      | none => simp [nextDigits, hn] at h
      | some pair =>
        rcases pair with ⟨tail, rest⟩
        simp only [nextDigits, hn, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [List.length_cons, ih hn]

theorem nextDigits_budget {digits next : List ℕ} {budget remaining : ℕ}
    (h : nextDigits digits budget = some (next, remaining)) :
    next.sum + remaining = digits.sum + budget := by
  induction digits generalizing next budget remaining with
  | nil => simp [nextDigits] at h
  | cons a digits ih =>
    cases budget with
    | succ budget =>
      simp only [nextDigits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.sum_cons]
      omega
    | zero =>
      cases hn : nextDigits digits a with
      | none => simp [nextDigits, hn] at h
      | some pair =>
        rcases pair with ⟨tail, rest⟩
        simp only [nextDigits, hn, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ht := ih hn
        simp only [List.sum_cons] at *
        omega

/-- Stack 0 is the reversed exponent word; stack 1 is the remaining budget;
stack 2 counts coordinates already reset during a carry.  Register 2 reports
success.  The instruction table is independent of the number of coordinates. -/
abbrev nextProgram : Program 3 3 21 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![
    .pop 0 0 1 1,
    .branch 1 2 19,
    .pop 1 0 1 3,
    .branch 1 4 8,
    .set 0 true 5,
    .push 0 0 6,
    .set 0 false 7,
    .push 0 0 15,
    .peek 0 0 1 9,
    .branch 1 10 13,
    .branch 0 11 13,
    .pop 0 0 1 12,
    .push 1 0 8,
    .set 0 false 14,
    .push 2 0 0,
    .pop 2 0 1 16,
    .branch 1 17 18,
    .push 0 0 15,
    .set 2 true 20,
    .set 2 false 20,
    .halt]

/-- Mathematical summary of one call, including its actual branch-dependent
instruction count.  This record is not evaluated by a machine instruction. -/
structure Result where
  digits : List ℕ
  budget : ℕ
  pending : ℕ
  found : Bool
  ticks : ℕ

def nextResult : List ℕ → ℕ → ℕ → Result
  | [], budget, pending => ⟨[], budget, pending, false, 4⟩
  | a :: digits, budget + 1, pending =>
      ⟨List.replicate pending 0 ++ (a + 1) :: digits, budget, 0, true,
        3 * pending + 12⟩
  | a :: digits, 0, pending =>
      let rest := nextResult digits a (pending + 1)
      { rest with ticks := 5 * a + (if digits = [] then 8 else 9) + rest.ticks }

theorem nextResult_spec (digits : List ℕ) (budget pending : ℕ) :
    match nextDigits digits budget with
    | none =>
      (nextResult digits budget pending).digits = [] ∧
      (nextResult digits budget pending).budget = budget + digits.sum ∧
      (nextResult digits budget pending).pending = pending + digits.length ∧
      (nextResult digits budget pending).found = false
    | some (next, remaining) =>
      (nextResult digits budget pending).digits = List.replicate pending 0 ++ next ∧
      (nextResult digits budget pending).budget = remaining ∧
      (nextResult digits budget pending).pending = 0 ∧
      (nextResult digits budget pending).found = true := by
  induction digits generalizing budget pending with
  | nil => simp [nextDigits, nextResult]
  | cons a digits ih =>
    cases budget with
    | succ budget => simp [nextDigits, nextResult]
    | zero =>
      have hi := ih a (pending + 1)
      cases hn : nextDigits digits a with
      | none =>
        simp only [hn] at hi
        simpa [nextDigits, hn, nextResult, List.sum_cons, List.length_cons,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
      | some pair =>
        rcases pair with ⟨next, remaining⟩
        simp only [hn] at hi
        simpa [nextDigits, hn, nextResult, List.replicate_add, List.append_assoc] using hi

theorem nextResult_success {digits next : List ℕ} {budget remaining : ℕ}
    (h : nextDigits digits budget = some (next, remaining)) :
    (nextResult digits budget 0).digits = next ∧
    (nextResult digits budget 0).budget = remaining ∧
    (nextResult digits budget 0).pending = 0 ∧
    (nextResult digits budget 0).found = true := by
  simpa [h] using nextResult_spec digits budget 0

theorem nextResult_bounded {digits next : List ℕ} {budget remaining bound : ℕ}
    (h : nextDigits digits budget = some (next, remaining))
    (hb : digits.sum + budget = bound) : next.sum ≤ bound := by
  have hs := nextDigits_budget h
  omega

theorem nextResult_ticks_le (digits : List ℕ) (budget pending : ℕ) :
    (nextResult digits budget pending).ticks ≤
      5 * digits.sum + 12 * digits.length + 3 * pending + 12 := by
  induction digits generalizing budget pending with
  | nil => simp [nextResult]
  | cons a digits ih =>
    cases budget with
    | succ budget => simp [nextResult]
    | zero =>
      have ht := ih a (pending + 1)
      simp only [nextResult, List.sum_cons, List.length_cons]
      split <;> omega

def storage (digits budget pending : List Bool) : Fin 3 → List Bool :=
  ![digits, budget, pending]

@[simp] theorem storage_zero (digits budget pending : List Bool) :
    storage digits budget pending 0 = digits := rfl
@[simp] theorem storage_one (digits budget pending : List Bool) :
    storage digits budget pending 1 = budget := rfl
@[simp] theorem storage_two (digits budget pending : List Bool) :
    storage digits budget pending 2 = pending := rfl

def cfg (pc : Option (Fin 21)) (regs : Fin 3 → Bool)
    (digits budget pending : List Bool) : Cfg 3 3 21 :=
  ⟨pc, regs, storage digits budget pending⟩

private theorem update_digits (xs ys zs next : List Bool) :
    Function.update (storage xs ys zs) 0 next = storage next ys zs := by
  funext i; fin_cases i <;> simp [storage]

private theorem update_budget (xs ys zs next : List Bool) :
    Function.update (storage xs ys zs) 1 next = storage xs next zs := by
  funext i; fin_cases i <;> simp [storage]

private theorem update_pending (xs ys zs next : List Bool) :
    Function.update (storage xs ys zs) 2 next = storage xs ys next := by
  funext i; fin_cases i <;> simp [storage]

private theorem read_twice (regs : Fin 3 → Bool) (a b : Option Bool) :
    readRegs (readRegs regs 0 1 a) 0 1 b = readRegs regs 0 1 b := by
  funext i; fin_cases i <;> simp [readRegs]

theorem empty_trace (regs : Fin 3 → Bool) (budget pending : List Bool) :
    Trace nextProgram 4 (cfg (some 0) regs [] budget pending)
      (cfg none (Function.update (readRegs regs 0 1 none) 2 false)
        [] budget pending) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, nextProgram, execInstr, cfg,
    readRegs, Function.update_apply, storage]

theorem success_prefix (regs : Fin 3 → Bool) (a budget : ℕ)
    (digits : List ℕ) (pending : List Bool) :
    Trace nextProgram 8
      (cfg (some 0) regs (digitsCode (a :: digits))
        (List.replicate (budget + 1) true) pending)
      (cfg (some 15) (readRegs regs 0 1 (some false))
        (digitsCode ((a + 1) :: digits)) (List.replicate budget true) pending) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, nextProgram, execInstr, cfg,
    digitsCode_cons, List.replicate_succ, readRegs, Function.update_apply,
    storage]
  constructor <;> funext i <;> fin_cases i <;> simp

theorem success_finish (regs : Fin 3 → Bool) (digits budget : List Bool) :
    Trace nextProgram 2 (cfg (some 18) regs digits budget [])
      (cfg none (Function.update regs 2 true) digits budget []) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, nextProgram, execInstr, cfg]

theorem success_trace (regs : Fin 3 → Bool) (a budget pending : ℕ)
    (digits : List ℕ) :
    ∃ finalRegs, finalRegs 2 = true ∧
      Trace nextProgram (3 * pending + 12)
        (cfg (some 0) regs (digitsCode (a :: digits))
          (List.replicate (budget + 1) true) (List.replicate pending false))
        (cfg none finalRegs
          (digitsCode (List.replicate pending 0 ++ (a + 1) :: digits))
          (List.replicate budget true) []) := by
  let middle := readRegs regs 0 1 (some false)
  let after := readRegs middle 0 1 none
  have h₁ := success_prefix regs a budget digits (List.replicate pending false)
  have h₂ := StackRoutines.transfer_trace nextProgram (2 : Fin 3) 0 (0 : Fin 3) 1
    15 16 17 18 (by decide) (by decide) rfl rfl rfl middle
    (storage (digitsCode ((a + 1) :: digits)) (List.replicate budget true)
      (List.replicate pending false))
  have h₂' : Trace nextProgram (3 * pending + 2)
      (cfg (some 15) middle (digitsCode ((a + 1) :: digits))
        (List.replicate budget true) (List.replicate pending false))
      (cfg (some 18) after
        (digitsCode (List.replicate pending 0 ++ (a + 1) :: digits))
        (List.replicate budget true) []) := by
    simpa [cfg, StackRoutines.transferResult, StackRoutines.transferStacks,
      update_pending, update_digits, digitsCode_append, after] using h₂
  have h₃ := success_finish after
    (digitsCode (List.replicate pending 0 ++ (a + 1) :: digits))
    (List.replicate budget true)
  refine ⟨Function.update after 2 true, by simp, ?_⟩
  have total := (h₁.trans h₂').trans h₃
  convert total using 1
  omega

theorem carry_prefix (regs : Fin 3 → Bool) (a : ℕ)
    (digits : List ℕ) (pending : List Bool) :
    Trace nextProgram 4
      (cfg (some 0) regs (digitsCode (a :: digits)) [] pending)
      (cfg (some 8) (readRegs regs 0 1 none)
        (List.replicate a true ++ digitsCode digits) [] pending) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, nextProgram, execInstr, cfg,
    digitsCode_cons, readRegs, Function.update_apply, storage]
  constructor <;> funext i <;> fin_cases i <;> simp

theorem carry_true (regs : Fin 3 → Bool) (digits budget pending : List Bool) :
    Trace nextProgram 5
      (cfg (some 8) regs (true :: digits) budget pending)
      (cfg (some 8) (readRegs regs 0 1 (some true)) digits (true :: budget) pending) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, nextProgram, execInstr, cfg,
    readRegs, Function.update_apply, storage]
  constructor <;> funext i <;> fin_cases i <;> simp

theorem carry_scan (regs : Fin 3 → Bool) (a budget : ℕ)
    (digits : List ℕ) (pending : List Bool) :
    Trace nextProgram (5 * a + if digits = [] then 2 else 3)
      (cfg (some 8) regs (List.replicate a true ++ digitsCode digits)
        (List.replicate budget true) pending)
      (cfg (some 13) (readRegs regs 0 1 (digitsCode digits).head?)
        (digitsCode digits) (List.replicate (a + budget) true) pending) := by
  induction a generalizing regs budget with
  | zero =>
    cases digits with
    | nil =>
      apply SubexponentialSAT.Computation.Trace.of_iterate
      simp [Function.iterate_succ_apply, step, nextProgram, execInstr, cfg,
        readRegs, storage]
    | cons b digits =>
      apply SubexponentialSAT.Computation.Trace.of_iterate
      simp [Function.iterate_succ_apply, step, nextProgram, execInstr, cfg,
        digitsCode_cons, readRegs, storage]
  | succ a ih =>
    have h₁ := carry_true regs (List.replicate a true ++ digitsCode digits)
      (List.replicate budget true) pending
    have h₂ := ih (readRegs regs 0 1 (some true)) (budget + 1)
    have total := h₁.trans (by simpa [List.replicate_succ] using h₂)
    have he : a + (budget + 1) = (a + 1) + budget := by omega
    simp only [read_twice, he] at total
    simp only [List.replicate_succ, List.cons_append]
    convert total using 1
    omega

theorem carry_suffix (regs : Fin 3 → Bool) (digits budget pending : List Bool) :
    Trace nextProgram 2
      (cfg (some 13) regs digits budget pending)
      (cfg (some 0) (Function.update regs 0 false) digits budget (false :: pending)) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, nextProgram, execInstr, cfg,
    Function.update_apply, storage]
  funext i; fin_cases i <;> simp

/-- Exact finite-instruction execution of the budget-spending successor. -/
theorem next_trace (digits : List ℕ) (budget pending : ℕ) (regs : Fin 3 → Bool) :
    ∃ finalRegs, finalRegs 2 = (nextResult digits budget pending).found ∧
      Trace nextProgram (nextResult digits budget pending).ticks
        (cfg (some 0) regs (digitsCode digits) (List.replicate budget true)
          (List.replicate pending false))
        (cfg none finalRegs (digitsCode (nextResult digits budget pending).digits)
          (List.replicate (nextResult digits budget pending).budget true)
          (List.replicate (nextResult digits budget pending).pending false)) := by
  induction digits generalizing budget pending regs with
  | nil =>
    refine ⟨Function.update (readRegs regs 0 1 none) 2 false, by simp [nextResult], ?_⟩
    simpa [nextResult] using empty_trace regs (List.replicate budget true)
      (List.replicate pending false)
  | cons a digits ih =>
    cases budget with
    | succ budget =>
      simpa [nextResult] using success_trace regs a budget pending digits
    | zero =>
      let r₁ := readRegs regs 0 1 none
      let r₂ := readRegs r₁ 0 1 (digitsCode digits).head?
      let r₃ := Function.update r₂ 0 false
      have h₁ := carry_prefix regs a digits (List.replicate pending false)
      have h₂ := carry_scan r₁ a 0 digits (List.replicate pending false)
      have h₃ := carry_suffix r₂ (digitsCode digits) (List.replicate a true)
        (List.replicate pending false)
      obtain ⟨finalRegs, hflag, h₄⟩ := ih a (pending + 1) r₃
      refine ⟨finalRegs, hflag, ?_⟩
      have total := ((h₁.trans (by simpa using h₂)).trans h₃).trans
        (by simpa [List.replicate_succ] using h₄)
      change Trace nextProgram
        (5 * a + (if digits = [] then 8 else 9) + (nextResult digits a (pending + 1)).ticks)
        (cfg (some 0) regs (digitsCode (a :: digits)) []
          (List.replicate pending false))
        (cfg none finalRegs (digitsCode (nextResult digits a (pending + 1)).digits)
          (List.replicate (nextResult digits a (pending + 1)).budget true)
          (List.replicate (nextResult digits a (pending + 1)).pending false))
      convert total using 1
      split <;> omega

theorem next_runsIn (digits : List ℕ) (budget pending : ℕ) (regs : Fin 3 → Bool) :
    ∃ finalRegs, finalRegs 2 = (nextResult digits budget pending).found ∧
      RunsIn nextProgram (5 * digits.sum + 12 * digits.length + 3 * pending + 12)
        (cfg (some 0) regs (digitsCode digits) (List.replicate budget true)
          (List.replicate pending false))
        (cfg none finalRegs (digitsCode (nextResult digits budget pending).digits)
          (List.replicate (nextResult digits budget pending).budget true)
          (List.replicate (nextResult digits budget pending).pending false)) := by
  obtain ⟨finalRegs, hflag, ht⟩ := next_trace digits budget pending regs
  exact ⟨finalRegs, hflag, _, nextResult_ticks_le digits budget pending, ht⟩

end SubexponentialSAT.SubexpExponentSuccessor

end OAI.Algorithms
