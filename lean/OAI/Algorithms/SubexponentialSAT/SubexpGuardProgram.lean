import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSchedule
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.ModularArithmetic

namespace OAI.Algorithms

/-!
# Concrete binary guard control for the subexponential schedule

The comparator below has a fixed instruction table, reads arbitrary-width
little-endian binary words, and uses only Boolean operations and stack pops.
Schedule arithmetic is not an instruction of this program.
-/

namespace SubexponentialSAT.SubexpGuardProgram

open BitProgram BinaryArithmetic

namespace Compare

/-- Borrow propagation with implicit high zero bits. -/
def carry (c : Bool) : List Bool → List Bool → Bool
  | [], [] => c
  | a :: xs, [] => carry (ModularArithmetic.borrowBit a false c) xs []
  | [], b :: ys => carry (ModularArithmetic.borrowBit false b c) [] ys
  | a :: xs, b :: ys => carry (ModularArithmetic.borrowBit a b c) xs ys
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
        simp [ModularArithmetic.borrowBit, bitVal, BinaryArithmetic.toNat]
  | cons a xs ih =>
    cases ys with
    | nil =>
      rw [carry, ih]
      cases a <;> cases c <;>
        simp [ModularArithmetic.borrowBit, bitVal, BinaryArithmetic.toNat]
    | cons b ys =>
      rw [carry, ih]
      cases a <;> cases b <;> cases c <;>
        simp [ModularArithmetic.borrowBit, bitVal, BinaryArithmetic.toNat] <;> omega

/-- Eight one-bit registers, two stacks, and twelve fixed labels. Register zero
is the result; both operand stacks are consumed. Entry resets the borrow bit. -/
abbrev program : Program 8 2 12 where
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

abbrev cfg (pc : Option (Fin 12)) (regs : Fin 8 → Bool) (xs ys : List Bool) : Cfg 8 2 12 :=
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
    roundRegs regs a b 0 = ModularArithmetic.borrowBit (a.getD false) (b.getD false) (regs 0) := by
  simp only [roundRegs, Function.update_self]
  cases ha : a.getD false <;> cases hb : b.getD false <;> cases hc : regs 0 <;>
    simp [ ModularArithmetic.borrowBit]

private theorem round_trace_false_false (regs : Fin 8 → Bool) (xs ys : List Bool) :
    Trace program 10 (cfg (some 1) regs (false :: xs) (false :: ys))
      (cfg (some 1) (roundRegs regs (some false) (some false)) xs ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

private theorem round_trace_false_true (regs : Fin 8 → Bool) (xs ys : List Bool) :
    Trace program 10 (cfg (some 1) regs (false :: xs) (true :: ys))
      (cfg (some 1) (roundRegs regs (some false) (some true)) xs ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

private theorem round_trace_true_false (regs : Fin 8 → Bool) (xs ys : List Bool) :
    Trace program 10 (cfg (some 1) regs (true :: xs) (false :: ys))
      (cfg (some 1) (roundRegs regs (some true) (some false)) xs ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

private theorem round_trace_true_true (regs : Fin 8 → Bool) (xs ys : List Bool) :
    Trace program 10 (cfg (some 1) regs (true :: xs) (true :: ys))
      (cfg (some 1) (roundRegs regs (some true) (some true)) xs ys) := by
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
    | cons b ys =>
      cases b <;> apply Computation.Trace.of_iterate <;>
        simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
          read, roundRegs, readRegs, update_left, update_right, Function.update_apply]
  | cons a xs =>
    cases ys with
    | nil =>
      cases a <;> apply Computation.Trace.of_iterate <;>
        simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
          read, roundRegs, readRegs, update_left, update_right, Function.update_apply]
    | cons b ys =>
      cases a <;> cases b
      · exact round_trace_false_false regs xs ys
      · exact round_trace_false_true regs xs ys
      · exact round_trace_true_false regs xs ys
      · exact round_trace_true_true regs xs ys

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
      (b.regs (register 0) = true ↔ BinaryArithmetic.toNat (a.stacks (stack 0)) < BinaryArithmetic.toNat (a.stacks (stack 1))) ∧
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

/-- The accumulator lives outside the comparator's eight work registers. -/
def workRegister (i : Fin 8) : Fin 9 := Fin.castAdd 1 i

def pairStack (j : Fin 3) (i : Fin 2) : Fin 6 := ⟨2 * j.val + i.val, by omega⟩

private theorem workRegister_injective : Function.Injective workRegister := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 9 => x.val) h

private theorem pairStack_injective (j : Fin 3) : Function.Injective (pairStack j) := by
  intro i k h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [pairStack] at this
  omega

private theorem accumulator_not_work : ¬ ∃ i, workRegister i = (8 : Fin 9) := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  change i.val = 8 at this
  have hi := i.isLt
  omega

/-- Compare one pair, invert strict-less, and conjoin the result into register 8. -/
abbrev checkPair (j : Fin 3) : StructuredCalls.Cmd 9 6 :=
  .seq (.call (ProgramLinking.liftProgram Compare.program workRegister (pairStack j)))
    (.base (.seq (.atom (.bnot 0 0)) (.atom (.band 8 8 0))))

def pairCost (j : Fin 3) (a : State 9 6) : ℕ :=
  10 * max (a.stacks (pairStack j 0)).length (a.stacks (pairStack j 1)).length + 8

def pairPass (j : Fin 3) (a : State 9 6) : Bool :=
  decide (BinaryArithmetic.toNat (a.stacks (pairStack j 1)) ≤ BinaryArithmetic.toNat (a.stacks (pairStack j 0)))

/-- Concrete comparison-and-accumulation contract. Pair operands are consumed;
all other stacks, including a caller's retained copies, are preserved. -/
theorem checkPair_eval (j : Fin 3) (a : State 9 6) :
    ∃ b : State 9 6, StructuredCalls.Eval (checkPair j) (pairCost j a) a b ∧
      b.regs 8 = (a.regs 8 && pairPass j a) ∧
      (∀ i, (¬ ∃ h, pairStack j h = i) → b.stacks i = a.stacks i) ∧
      (∀ h, b.stacks (pairStack j h) = []) := by
  obtain ⟨mid, hrun, hcmp, hregs, hstacks, hclear⟩ :=
    compare_call workRegister (pairStack j) workRegister_injective (pairStack_injective j) a
  let inv := (Atom.bnot (0 : Fin 9) 0).eval mid
  let b := (Atom.band (8 : Fin 9) 8 0).eval inv
  have heval : StructuredProgram.Eval
      (.seq (.atom (.bnot 0 0)) (.atom (.band 8 8 0))) 2 mid b :=
    .seq (.atom _ _) (.atom _ _)
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · have h := StructuredCalls.Eval.seq hrun (StructuredCalls.Eval.base heval)
    simpa only [checkPair, pairCost, Nat.add_assoc] using h
  · have hacc := hregs 8 accumulator_not_work
    have hbool : (!mid.regs 0) = pairPass j a := by
      change mid.regs 0 = true ↔ _ at hcmp
      cases hm : mid.regs 0 with
      | false =>
        have hn : BinaryArithmetic.toNat (a.stacks (pairStack j 1)) ≤ BinaryArithmetic.toNat (a.stacks (pairStack j 0)) := by
          have hnot : ¬ BinaryArithmetic.toNat (a.stacks (pairStack j 0)) < BinaryArithmetic.toNat (a.stacks (pairStack j 1)) := by
            simpa [hm] using hcmp.symm
          omega
        simp [ pairPass, hn]
      | true =>
        have hn : ¬ BinaryArithmetic.toNat (a.stacks (pairStack j 1)) ≤ BinaryArithmetic.toNat (a.stacks (pairStack j 0)) := by
          have hlt := hcmp.mp hm
          omega
        simp [ pairPass, hn]
    simp [b, inv, Atom.eval, Atom.instr, State.ofCfg,
      execInstr, hacc, hbool]
  · intro i hi
    exact hstacks i hi
  · exact hclear

private theorem pair_disjoint {j k : Fin 3} (hjk : j ≠ k) (i : Fin 2) :
    ¬ ∃ h, pairStack j h = pairStack k i := by
  rintro ⟨h, heq⟩
  have hv := congrArg Fin.val heq
  apply hjk
  apply Fin.ext
  simp only [pairStack] at hv
  omega

private theorem pair_views_frame {j k : Fin 3} (hjk : j ≠ k) {a b : State 9 6}
    (hframe : ∀ i, (¬ ∃ h, pairStack j h = i) → b.stacks i = a.stacks i) :
    pairCost k b = pairCost k a ∧ pairPass k b = pairPass k a := by
  have h0 := hframe (pairStack k 0) (pair_disjoint hjk 0)
  have h1 := hframe (pairStack k 1) (pair_disjoint hjk 1)
  simp only [pairCost, pairPass, h0, h1, and_self]

/-- Fixed control: initialize the accumulator and check the three numeric pairs. -/
abbrev guard : StructuredCalls.Cmd 9 6 :=
  .seq (.base (.atom (.set 8 true)))
    (.seq (checkPair 0) (.seq (checkPair 1) (checkPair 2)))

def guardCost (a : State 9 6) : ℕ := 1 + pairCost 0 a + pairCost 1 a + pairCost 2 a

def guardPass (a : State 9 6) : Bool :=
  (pairPass 0 a && pairPass 1 a) && pairPass 2 a

/-- All three numeric comparisons execute as one fixed structured program. -/
theorem guard_eval (a : State 9 6) :
    ∃ b : State 9 6, StructuredCalls.Eval guard (guardCost a) a b ∧
      b.regs 8 = guardPass a := by
  let a0 := (Atom.set (8 : Fin 9) true).eval a
  have hinit : StructuredCalls.Eval (.base (.atom (.set 8 true))) 1 a a0 :=
    .base (.atom _ _)
  obtain ⟨a1, he0, hr0, hf0, _⟩ := checkPair_eval 0 a0
  obtain ⟨a2, he1, hr1, hf1, _⟩ := checkPair_eval 1 a1
  obtain ⟨a3, he2, hr2, _, _⟩ := checkPair_eval 2 a2
  have hv01 := pair_views_frame (j := 0) (k := 1) (by decide) hf0
  have hv02 := pair_views_frame (j := 0) (k := 2) (by decide) hf0
  have hv12 := pair_views_frame (j := 1) (k := 2) (by decide) hf1
  have hcost0 : pairCost 0 a0 = pairCost 0 a := rfl
  have hcost1 : pairCost 1 a1 = pairCost 1 a := hv01.1
  have hcost2 : pairCost 2 a2 = pairCost 2 a := hv12.1.trans hv02.1
  have hpass0 : pairPass 0 a0 = pairPass 0 a := rfl
  have hpass1 : pairPass 1 a1 = pairPass 1 a := hv01.2
  have hpass2 : pairPass 2 a2 = pairPass 2 a := hv12.2.trans hv02.2
  have hacc : a0.regs 8 = true := by
    simp [a0, Atom.eval, Atom.instr, State.ofCfg, execInstr]
  refine ⟨a3, ?_, ?_⟩
  · have h := StructuredCalls.Eval.seq hinit
      (StructuredCalls.Eval.seq he0 (StructuredCalls.Eval.seq he1 he2))
    simpa only [guard, guardCost, hcost0, hcost1, hcost2, Nat.add_assoc] using h
  · rw [hr2, hr1, hr0, hacc, hpass0, hpass1, hpass2]
    rfl

/-- The caller supplies already-computed binary encodings of the five numeric
quantities and the constant 32. This is a data relation, never an instruction. -/
structure EncodesChecks (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (a : State 9 6) : Prop where
  s_value : BinaryArithmetic.toNat (a.stacks 0) = SubexpPackingParameters.s n
  threshold_value : BinaryArithmetic.toNat (a.stacks 1) = 32
  tail_right : BinaryArithmetic.toNat (a.stacks 2) = SubexpSchedule.R k hk n ^ 2
  tail_left : BinaryArithmetic.toNat (a.stacks 3) =
    16 * SubexpSchedule.Q n * SubexpSchedule.delta k hk n * SubexpPackingParameters.s n
  dimension : BinaryArithmetic.toNat (a.stacks 4) = SubexpPackingParameters.D n
  threshold : BinaryArithmetic.toNat (a.stacks 5) = SubexpSchedule.Dstar k hk n

/-- The bit produced by the concrete guard is precisely the source readiness
predicate, once the independently computed numeric operands are represented. -/
theorem guardPass_iff_ready {k n : ℕ} {hk : 2 ≤ k} {a : State 9 6}
    (h : EncodesChecks k hk n a) : guardPass a = true ↔ SubexpSchedule.Ready k hk n := by
  simp only [guardPass, Bool.and_eq_true, pairPass, decide_eq_true_eq]
  change ((BinaryArithmetic.toNat (a.stacks 1) ≤ BinaryArithmetic.toNat (a.stacks 0) ∧
      BinaryArithmetic.toNat (a.stacks 3) ≤ BinaryArithmetic.toNat (a.stacks 2)) ∧
      BinaryArithmetic.toNat (a.stacks 5) ≤ BinaryArithmetic.toNat (a.stacks 4)) ↔ _
  rw [h.s_value, h.threshold_value, h.tail_left, h.tail_right, h.threshold, h.dimension]
  exact and_assoc

theorem guard_eval_schedule {k n : ℕ} {hk : 2 ≤ k} {a : State 9 6}
    (h : EncodesChecks k hk n a) :
    ∃ b : State 9 6, StructuredCalls.Eval guard (guardCost a) a b ∧
      (b.regs 8 = true ↔ SubexpSchedule.Ready k hk n) := by
  obtain ⟨b, hr, hv⟩ := guard_eval a
  exact ⟨b, hr, hv ▸ guardPass_iff_ready h⟩

/-- Both continuations are actual structured programs; the test is one actual
Boolean branch instruction after executing the numeric guard. -/
abbrev dispatch (yes no : StructuredCalls.Cmd 9 6) : StructuredCalls.Cmd 9 6 :=
  .seq guard (.ite 8 yes no)

theorem dispatch_eval (a : State 9 6) (yes no : StructuredCalls.Cmd 9 6) :
    ∃ mid : State 9 6, mid.regs 8 = guardPass a ∧
      ∀ (m : ℕ) (b : State 9 6),
        StructuredCalls.Eval (if guardPass a then yes else no) m mid b →
        StructuredCalls.Eval (dispatch yes no) (guardCost a + (m + 1)) a b := by
  obtain ⟨mid, hg, hv⟩ := guard_eval a
  refine ⟨mid, hv, ?_⟩
  intro m b hb
  apply StructuredCalls.Eval.seq hg
  cases ht : guardPass a with
  | false =>
    apply StructuredCalls.Eval.ite_false (hv.trans ht)
    simpa [ht] using hb
  | true =>
    apply StructuredCalls.Eval.ite_true (hv.trans ht)
    simpa [ht] using hb

/-- Compilation yields an actual primitive execution between the corresponding
encoded internal configurations, with fixed program-dependent overhead. -/
theorem guard_primitive_execution (a : State 9 6) :
    ∃ b : State 9 6, b.regs 8 = guardPass a ∧
      let p := StructuredCalls.compiled guard 0 1
      Computation.RunsIn (BitProgram.primitive p).step
        (BitProgram.primitiveOverhead p * (guardCost a + 1))
        (BitProgram.primitiveCfg p (a.withPC (some p.entry)))
        (BitProgram.primitiveCfg p (b.withPC none)) := by
  obtain ⟨b, he, hv⟩ := guard_eval a
  exact ⟨b, hv, StructuredCalls.primitive_execution he 0 1⟩


/-- Eight physical instructions write the little-endian word for 32. -/
abbrev loadThirtyTwo {r s : ℕ} (scratch : Fin r) (target : Fin s) : StructuredProgram.Cmd r s :=
  .seq (.atom (.set scratch true))
    (.seq (.atom (.push target scratch))
      (.seq (.atom (.set scratch false))
        (.seq (.atom (.push target scratch))
          (.seq (.atom (.push target scratch))
            (.seq (.atom (.push target scratch))
              (.seq (.atom (.push target scratch)) (.atom (.push target scratch))))))))

def loadThirtyTwoState {r s : ℕ} (scratch : Fin r) (target : Fin s) (a : State r s) :
    State r s :=
  ⟨Function.update a.regs scratch false,
    Function.update a.stacks target ([false, false, false, false, false, true] ++ a.stacks target)⟩

theorem loadThirtyTwo_eval {r s : ℕ} (scratch : Fin r) (target : Fin s) (a : State r s) :
    StructuredProgram.Eval (loadThirtyTwo scratch target) 8 a
      (loadThirtyTwoState scratch target a) := by
  have h := StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.set scratch true) a)
    (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.push target scratch) _)
      (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.set scratch false) _)
        (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.push target scratch) _)
          (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.push target scratch) _)
            (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.push target scratch) _)
              (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.push target scratch) _)
                (StructuredProgram.Eval.atom (.push target scratch) _)))))))
  simpa [loadThirtyTwo, loadThirtyTwoState, Atom.eval, Atom.instr,
    State.ofCfg, State.withPC, execInstr] using h

theorem loadThirtyTwo_value {r s : ℕ} (scratch : Fin r) (target : Fin s) (a : State r s)
    (hempty : a.stacks target = []) :
    BinaryArithmetic.toNat ((loadThirtyTwoState scratch target a).stacks target) = 32 := by
  simp [loadThirtyTwoState, hempty, BinaryArithmetic.toNat, bitVal]

theorem loadThirtyTwo_frame {r s : ℕ} (scratch : Fin r) (target : Fin s) (a : State r s)
    (i : Fin s) (hi : i ≠ target) :
    (loadThirtyTwoState scratch target a).stacks i = a.stacks i := by
  simp [loadThirtyTwoState, hi]

/-- The first guard can run before the remaining schedule arithmetic. -/
abbrev earlyGuard : StructuredCalls.Cmd 9 6 :=
  .seq (.base (loadThirtyTwo 0 1))
    (.seq (.base (.atom (.set 8 true))) (checkPair 0))

def earlyGuardCost (a : State 9 6) : ℕ :=
  10 * max (a.stacks 0).length 6 + 17

theorem earlyGuard_eval (a : State 9 6) (hempty : a.stacks 1 = []) :
    ∃ b : State 9 6, StructuredCalls.Eval earlyGuard (earlyGuardCost a) a b ∧
      (b.regs 8 = true ↔ 32 ≤ BinaryArithmetic.toNat (a.stacks 0)) ∧
      (∀ i : Fin 6, i ≠ 0 → i ≠ 1 → b.stacks i = a.stacks i) ∧
      b.stacks 0 = [] ∧ b.stacks 1 = [] := by
  let loaded := loadThirtyTwoState (0 : Fin 9) (1 : Fin 6) a
  let initialized := (Atom.set (8 : Fin 9) true).eval loaded
  obtain ⟨b, hpair, hbit, hframe, hclear⟩ := checkPair_eval 0 initialized
  have hload : StructuredCalls.Eval (.base (loadThirtyTwo 0 1)) 8 a loaded :=
    .base (loadThirtyTwo_eval 0 1 a)
  have hinit : StructuredCalls.Eval (.base (.atom (.set 8 true))) 1 loaded initialized :=
    .base (.atom _ _)
  have hcost : pairCost 0 initialized = 10 * max (a.stacks 0).length 6 + 8 := by
    simp [pairCost, pairStack, initialized, loaded, loadThirtyTwoState,
      Atom.eval, Atom.instr, State.ofCfg, execInstr, hempty]
  have hpass : pairPass 0 initialized = decide (32 ≤ BinaryArithmetic.toNat (a.stacks 0)) := by
    simp [pairPass, pairStack, initialized, loaded, loadThirtyTwoState,
      Atom.eval, Atom.instr, State.ofCfg, execInstr, hempty, BinaryArithmetic.toNat, bitVal]
  have hacc : initialized.regs 8 = true := by
    simp [initialized, Atom.eval, Atom.instr, State.ofCfg, execInstr]
  refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
  · have h := StructuredCalls.Eval.seq hload (StructuredCalls.Eval.seq hinit hpair)
    rw [hcost] at h
    have hcount : 8 + (1 + (10 * max (a.stacks 0).length 6 + 8)) = earlyGuardCost a := by
      unfold earlyGuardCost
      omega
    rw [hcount] at h
    exact h
  · rw [hbit, hacc, hpass]
    simp
  · intro i hi0 hi1
    have hn : ¬ ∃ h, pairStack 0 h = i := by
      rintro ⟨h, rfl⟩
      fin_cases h <;> simp [pairStack] at hi0 hi1
    rw [hframe i hn]
    simpa [initialized, Atom.eval, Atom.instr, State.ofCfg, State.withPC,
      execInstr, loaded] using loadThirtyTwo_frame 0 1 a i hi1
  · exact hclear 0
  · exact hclear 1

theorem earlyGuard_eval_schedule {n : ℕ} (a : State 9 6) (hempty : a.stacks 1 = [])
    (hs : BinaryArithmetic.toNat (a.stacks 0) = SubexpPackingParameters.s n) :
    ∃ b : State 9 6, StructuredCalls.Eval earlyGuard (earlyGuardCost a) a b ∧
      (b.regs 8 = true ↔ SubexpPackingParameters.GoodInput n) ∧
      (∀ i : Fin 6, i ≠ 0 → i ≠ 1 → b.stacks i = a.stacks i) ∧
      b.stacks 0 = [] ∧ b.stacks 1 = [] := by
  simpa only [hs, SubexpPackingParameters.GoodInput] using earlyGuard_eval a hempty


end SubexponentialSAT.SubexpGuardProgram

end OAI.Algorithms
