import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace OAI.Algorithms

/-!
# A primitive implementation of the final positivity test

The same seven-label program scans every little-endian Boolean word.  It
returns true exactly when the encoded natural number is positive.  It may
leave an unused suffix after finding a one bit; only the output head is read
by the already verified primitive compiler.
-/

namespace SubexponentialSAT.PositiveWordProgram

open BitProgram

def positive : List Bool → Bool
  | [] => false
  | false :: xs => positive xs
  | true :: _ => true

def residual : List Bool → List Bool
  | [] => []
  | false :: xs => residual xs
  | true :: xs => xs

def cost : List Bool → ℕ
  | [] => 5
  | false :: xs => cost xs + 3
  | true :: _ => 6

theorem positive_iff (xs : List Bool) :
    positive xs = true ↔ 0 < BinaryArithmetic.toNat xs := by
  induction xs with
  | nil => simp [positive]
  | cons x xs ih =>
      cases x <;> simp [positive, BinaryArithmetic.toNat, ih]

/-- The same concrete scan is an OR over an explicitly materialized list of
leaf answers. Construction of that list is a separate phase. -/
theorem positive_eq_true_iff_mem (xs : List Bool) :
    positive xs = true ↔ true ∈ xs := by
  induction xs with
  | nil => simp [positive]
  | cons x xs ih => cases x <;> simp [positive, ih]

theorem positive_map_iff {α : Type*} (test : α → Bool) (xs : List α) :
    positive (xs.map test) = true ↔ ∃ x ∈ xs, test x = true := by
  rw [positive_eq_true_iff_mem, List.mem_map]

theorem cost_le (xs : List Bool) : cost xs ≤ 3 * xs.length + 5 := by
  induction xs with
  | nil => simp [cost]
  | cons x xs ih => cases x <;> simp only [cost, List.length_cons] <;> omega

abbrev program : Program 2 1 7 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 4
    | 2 => .branch 0 3 0
    | 3 => .set 0 true 5
    | 4 => .set 0 false 5
    | 5 => .push 0 0 6
    | _ => .halt

def regs (value present : Bool) : Fin 2 → Bool :=
  fun i => if i = 0 then value else present

@[simp] theorem update_regs_zero (v p b : Bool) :
    Function.update (regs v p) 0 b = regs b p := by
  funext i
  fin_cases i <;> simp [regs]

@[simp] theorem update_regs_one (v p b : Bool) :
    Function.update (regs v p) 1 b = regs v b := by
  funext i
  fin_cases i <;> simp [regs]

@[simp] theorem update_stack (xs ys : List Bool) :
    Function.update (fun _ : Fin 1 => xs) 0 ys = fun _ => ys := by
  funext i
  fin_cases i
  simp

def cfg (pc : Option (Fin 7)) (v p : Bool) (xs : List Bool) : Cfg 2 1 7 :=
  ⟨pc, regs v p, fun _ => xs⟩

theorem run (xs : List Bool) (v p : Bool) :
    Trace program (cost xs) (cfg (some 0) v p xs)
      (cfg none (positive xs) (positive xs) (positive xs :: residual xs)) := by
  induction xs generalizing v p with
  | nil =>
      change Trace program 5 (cfg (some 0) v p []) (cfg none false false [false])
      refine .cons (b := cfg (some 1) false false []) ?_ ?_
      · simp [step, cfg, execInstr, readRegs]
      refine .cons (b := cfg (some 4) false false []) ?_ ?_
      · simp [step, cfg, execInstr, regs]
      refine .cons (b := cfg (some 5) false false []) ?_ ?_
      · simp [step, cfg, execInstr]
      refine .cons (b := cfg (some 6) false false [false]) ?_ ?_
      · simp [step, cfg, execInstr, regs]
      exact .cons rfl (.refl _)
  | cons x xs ih =>
      cases x with
      | false =>
          change Trace program (cost xs + 3) (cfg (some 0) v p (false :: xs)) _
          refine .cons (b := cfg (some 1) false true xs) ?_ ?_
          · simp [step, cfg, execInstr, readRegs]
          refine .cons (b := cfg (some 2) false true xs) ?_ ?_
          · simp [step, cfg, execInstr, regs]
          refine .cons (b := cfg (some 0) false true xs) ?_ (ih false true)
          simp [step, cfg, execInstr, regs]
      | true =>
          change Trace program 6 (cfg (some 0) v p (true :: xs))
            (cfg none true true (true :: xs))
          refine .cons (b := cfg (some 1) true true xs) ?_ ?_
          · simp [step, cfg, execInstr, readRegs]
          refine .cons (b := cfg (some 2) true true xs) ?_ ?_
          · simp [step, cfg, execInstr, regs]
          refine .cons (b := cfg (some 3) true true xs) ?_ ?_
          · simp [step, cfg, execInstr, regs]
          refine .cons (b := cfg (some 5) true true xs) ?_ ?_
          · simp [step, cfg, execInstr]
          refine .cons (b := cfg (some 6) true true (true :: xs)) ?_ ?_
          · simp [step, cfg, execInstr, regs]
          exact .cons rfl (.refl _)

theorem initial_eq (xs : List Bool) :
    initial program xs = cfg (some 0) false false xs := by
  simp only [initial, cfg]
  congr 1
  · funext i
    simp [regs]
  · funext i
    fin_cases i
    simp

theorem runsIn (xs : List Bool) :
    RunsIn program (3 * xs.length + 5) (initial program xs)
      (cfg none (positive xs) (positive xs) (positive xs :: residual xs)) := by
  rw [initial_eq]
  exact ⟨cost xs, cost_le xs, run xs false false⟩

/-- A genuine primitive-bit execution, not an arithmetic-operation estimate. -/
theorem primitive_outputs (xs : List Bool) :
    (primitive program).OutputsInTime xs (positive xs)
      (primitiveOverhead program * (3 * xs.length + 5)) := by
  exact primitive_outputs_of_halted program (runsIn xs) rfl rfl

theorem encoded_count_correct (xs : List Bool) (count : ℕ)
    (hvalue : BinaryArithmetic.toNat xs = count) :
    positive xs = true ↔ 0 < count := by
  rw [positive_iff, hvalue]

end SubexponentialSAT.PositiveWordProgram

end OAI.Algorithms
