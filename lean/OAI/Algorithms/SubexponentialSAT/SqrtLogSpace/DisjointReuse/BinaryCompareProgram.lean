import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import Mathlib.Tactic.FinCases

/-! Minimal actual binary comparison, extracted from SubexpGuardProgram.
Only the concrete Boolean borrow operation and fixed comparison machine are retained.
The source map and hashes are recorded in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

def borrowBit (a b borrow : Bool) : Bool :=
  ((!a) && (b || borrow)) || (b && borrow)

namespace Compare

/-- Borrow propagation with implicit high zero bits. -/
def carry (c : Bool) : List Bool → List Bool → Bool
  | [], [] => c
  | a :: xs, [] => carry (borrowBit a false c) xs []
  | [], b :: ys => carry (borrowBit false b c) [] ys
  | a :: xs, b :: ys => carry (borrowBit a b c) xs ys
termination_by xs ys => xs.length + ys.length

/-- The final borrow is the strict comparison, even for unequal word lengths. -/
theorem carry_iff (xs ys : List Bool) (c : Bool) :
    carry c xs ys = true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys + bitVal c := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [carry, bitVal]
    | cons b ys ih =>
      rw [carry, ih]
      cases b <;> cases c <;>
        simp [borrowBit, bitVal, BinaryArithmetic.toNat]
  | cons a xs ih =>
    cases ys with
    | nil =>
      rw [carry, ih]
      cases a <;> cases c <;>
        simp [borrowBit, bitVal, BinaryArithmetic.toNat]
    | cons b ys =>
      rw [carry, ih]
      cases a <;> cases b <;> cases c <;>
        simp [borrowBit, bitVal, BinaryArithmetic.toNat] <;> omega

/-- Eight one-bit registers, two stacks, and twelve fixed labels. Register zero
is the result; both operand stacks are consumed. Entry resets the borrow bit. -/
def program : Program 8 2 12 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 0 false 1
    | 1 => .pop 0 1 3 2
    | 2 => .pop 1 2 4 3
    | 3 => .bor 5 3 4 4
    | 4 => .branch 5 5 11
    | 5 => .bnot 6 1 6
    | 6 => .band 6 6 2 7
    | 7 => .bxor 7 1 2 8
    | 8 => .bnot 7 7 9
    | 9 => .band 7 7 0 10
    | 10 => .bor 0 6 7 1
    | _ => .halt

def operandStacks (xs ys : List Bool) (i : Fin 2) : List Bool :=
  if i = 0 then xs else ys

@[simp] theorem operandStacks_left (xs ys : List Bool) : operandStacks xs ys 0 = xs := rfl
@[simp] theorem operandStacks_right (xs ys : List Bool) : operandStacks xs ys 1 = ys := rfl

def cfg (pc : Option (Fin 12)) (regs : Fin 8 → Bool) (xs ys : List Bool) : Cfg 8 2 12 :=
  ⟨pc, regs, operandStacks xs ys⟩

private theorem update_left (xs ys zs : List Bool) :
    Function.update (operandStacks xs ys) 0 zs = operandStacks zs ys := by
  funext i
  fin_cases i <;> simp [operandStacks]

private theorem update_right (xs ys zs : List Bool) :
    Function.update (operandStacks xs ys) 1 zs = operandStacks xs zs := by
  funext i
  fin_cases i <;> simp [operandStacks]

def read (regs : Fin 8 → Bool) (a b : Option Bool) : Fin 8 → Bool :=
  readRegs (readRegs regs 1 3 a) 2 4 b

def roundRegs (regs : Fin 8 → Bool) (a b : Option Bool) : Fin 8 → Bool :=
  let r := read regs a b
  let r := Function.update r 5 (a.isSome || b.isSome)
  let r := Function.update r 6 (!a.getD false)
  let r := Function.update r 6 ((!a.getD false) && b.getD false)
  let r := Function.update r 7 (a.getD false ^^ b.getD false)
  let r := Function.update r 7 (!(a.getD false ^^ b.getD false))
  let r := Function.update r 7 ((!(a.getD false ^^ b.getD false)) && regs 0)
  Function.update r 0 (((!a.getD false) && b.getD false) ||
    ((!(a.getD false ^^ b.getD false)) && regs 0))

theorem roundRegs_borrow (regs : Fin 8 → Bool) (a b : Option Bool) :
    roundRegs regs a b 0 = borrowBit (a.getD false) (b.getD false) (regs 0) := by
  simp only [roundRegs, Function.update_self]
  cases ha : a.getD false <;> cases hb : b.getD false <;> cases hc : regs 0 <;>
    simp [borrowBit]

private theorem round_nil_cons (regs : Fin 8 → Bool) (b : Bool) (ys : List Bool) :
    Trace program 10 (cfg (some 1) regs [] (b :: ys))
      (cfg (some 1) (roundRegs regs none (some b)) [] ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

private theorem round_cons_nil (regs : Fin 8 → Bool) (a : Bool) (xs : List Bool) :
    Trace program 10 (cfg (some 1) regs (a :: xs) [])
      (cfg (some 1) (roundRegs regs (some a) none) xs []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

private theorem round_cons_cons (regs : Fin 8 → Bool) (a b : Bool) (xs ys : List Bool) :
    Trace program 10 (cfg (some 1) regs (a :: xs) (b :: ys))
      (cfg (some 1) (roundRegs regs (some a) (some b)) xs ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

/-- A concrete nonterminal round, including its branch instruction. -/
theorem round_trace (regs : Fin 8 → Bool) (xs ys : List Bool)
    (hne : xs ≠ [] ∨ ys ≠ []) :
    Trace program 10 (cfg (some 1) regs xs ys)
      (cfg (some 1) (roundRegs regs xs.head? ys.head?) xs.tail ys.tail) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at hne
    | cons b ys => exact round_nil_cons regs b ys
  | cons a xs =>
    cases ys with
    | nil => exact round_cons_nil regs a xs
    | cons b ys => exact round_cons_cons regs a b xs ys

def exitRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (read regs none none) 5 false

theorem exit_trace (regs : Fin 8 → Bool) :
    Trace program 5 (cfg (some 1) regs [] []) (cfg none (exitRegs regs) [] []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, exitRegs, readRegs, update_left, update_right,
    Function.update_apply]

@[simp] theorem exitRegs_borrow (regs : Fin 8 → Bool) : exitRegs regs 0 = regs 0 := by
  simp [exitRegs, read, readRegs]

/-- Exact instruction count for the data-dependent loop. -/
theorem loop_trace (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace program (10 * max xs.length ys.length + 5)
        (cfg (some 1) regs xs ys) (cfg none rf [] []) ∧
      rf 0 = carry (regs 0) xs ys := by
  induction xs generalizing ys regs with
  | nil =>
    induction ys generalizing regs with
    | nil =>
      exact ⟨exitRegs regs, by simpa using exit_trace regs, by simp [carry]⟩
    | cons b ys ih =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs none (some b))
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs [] (b :: ys) (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb
  | cons a xs ih =>
    cases ys with
    | nil =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs (some a) none) []
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs (a :: xs) [] (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb
    | cons b ys =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs (some a) (some b)) ys
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs (a :: xs) (b :: ys) (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb

/-- Complete comparator contract. Leading zero bits and unequal widths are allowed. -/
theorem run (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace program (10 * max xs.length ys.length + 6)
        (cfg (some program.entry) regs xs ys) (cfg none rf [] []) ∧
      (rf 0 = true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys) := by
  obtain ⟨rf, hr, hb⟩ := loop_trace (Function.update regs 0 false) xs ys
  refine ⟨rf, ?_, ?_⟩
  · have he : Trace program 1 (cfg (some program.entry) regs xs ys)
        (cfg (some 1) (Function.update regs 0 false) xs ys) := by
      exact .cons (by rfl) (.refl _)
    convert he.trans hr using 1
    omega
  · rw [hb]
    simpa only [Function.update_self, bitVal_false, Nat.add_zero] using carry_iff xs ys false

end Compare

open StructuredProgram

/-- Restrict caller data to the fixed ports of a subroutine. This is assertion
notation, not an instruction available to the program. -/
def restrictState {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 2 → Fin S)
    (a : State R S) : State 8 2 :=
  ⟨fun i => a.regs (register i), fun i => a.stacks (stack i)⟩

private theorem extend_restrict {α β γ : Type} (f : α → β) (hf : Function.Injective f)
    (g : β → γ) : Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    exact hf.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ hb

private theorem embed_restrict {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 2 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (a : State R S) :
    StructuredCalls.embedState register stack a (restrictState register stack a) = a := by
  unfold StructuredCalls.embedState restrictState
  change State.mk (Function.extend register (a.regs ∘ register) a.regs)
    (Function.extend stack (a.stacks ∘ stack) a.stacks) = a
  rw [extend_restrict register hr, extend_restrict stack hs]

private theorem pair_eta (f : Fin 2 → List Bool) : Compare.operandStacks (f 0) (f 1) = f := by
  funext i
  fin_cases i <;> rfl

/-- A measured comparison call on fixed injective ports, with every other
caller register and stack preserved. -/
theorem compare_call {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 2 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (a : State R S) :
    ∃ b : State R S,
      StructuredCalls.Eval (.call (ProgramLinking.liftProgram Compare.program register stack))
        (10 * max (a.stacks (stack 0)).length (a.stacks (stack 1)).length + 6) a b ∧
      (b.regs (register 0) = true ↔
        BinaryArithmetic.toNat (a.stacks (stack 0)) <
          BinaryArithmetic.toNat (a.stacks (stack 1))) ∧
      (∀ i, (¬ ∃ j, register j = i) → b.regs i = a.regs i) ∧
      (∀ i, (¬ ∃ j, stack j = i) → b.stacks i = a.stacks i) ∧
      (∀ j, b.stacks (stack j) = []) := by
  obtain ⟨rf, hrun, hcmp⟩ := Compare.run (fun i => a.regs (register i))
    (a.stacks (stack 0)) (a.stacks (stack 1))
  have hstack := pair_eta (fun i => a.stacks (stack i))
  have hempty : Compare.operandStacks [] [] = (fun _ : Fin 2 => []) := by
    simpa using pair_eta (fun _ : Fin 2 => [])
  simp only [Compare.cfg, hstack, hempty] at hrun
  let localOut : State 8 2 := ⟨rf, fun _ => []⟩
  let b := StructuredCalls.embedState register stack a localOut
  refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
  · have h := StructuredCalls.eval_call_lifted Compare.program register stack a hr hs
      (a := restrictState register stack a) (b := localOut) hrun
    rw [embed_restrict register stack hr hs a] at h
    exact h
  · simpa only [b, StructuredCalls.embedState_register register stack a localOut hr,
      localOut] using hcmp
  · exact fun i hi => StructuredCalls.embedState_register_frame register stack a localOut i hi
  · exact fun i hi => StructuredCalls.embedState_stack_frame register stack a localOut i hi
  · exact fun j => StructuredCalls.embedState_stack register stack a localOut hs j


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram
