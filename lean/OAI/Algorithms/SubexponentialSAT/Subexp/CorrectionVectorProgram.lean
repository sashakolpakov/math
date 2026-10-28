import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.CorrectionScalarCanonical

namespace OAI.Algorithms

/-! Fixed control for all Q correction coefficients, in increasing position
order.  Every coefficient is computed by the actual zero-extended entry
program, negated in the prime field, and embedded as a source-field quartet. -/

namespace SubexponentialSAT.Subexp.CorrectionVectorProgram

open scoped BigOperators
open BitProgram StructuredCalls StackRoutines BinaryArithmetic MatrixWordEncoding MulticolorTypes

abbrev Word := List Bool
abbrev Data := State 10 49
abbrev Code := Cmd 10 49

def entryMap : Fin 42 → Fin 49 := Fin.castAdd 7
theorem entryMap_injective : Function.Injective entryMap := Fin.castAdd_injective 42 7

def entry : Code := .call (ProgramLinking.liftProgram
  MatrixExtendedEntryProgram.program id entryMap)
def coefficient : Code := .seq entry CorrectionScalarProgram.command
def advance : Code := TupleProgram.pushConst 37 0 true
def peek : Code := .base (.atom (.peek 42 8 9))
def pop : Code := .base (.atom (.pop 42 8 9))
def body : Code := .seq pop (.seq coefficient (.seq advance peek))
def loop : Code := .while 9 body
def command : Code :=
  .seq (.call (copyProgram 22 42 44 (0 : Fin 10) 1))
    (.seq peek (.seq loop (.seq (.call (clearProgram 37 (0 : Fin 10) 1))
      (.call (transferProgram 43 48 (0 : Fin 10) 1)))))
abbrev program : Program 10 49 (size command + 1) := compiled command 23 48

variable {r Q Δ : ℕ}
variable (p : ℕ) [Fact p.Prime] (i : Fin Δ) (u y : UniversalType r Q Δ)
variable (xs : List (ZMod p))

def state (constant shape : Word) (regs : Fin 10 → Bool) (j n : ℕ) (out : Word) : Data :=
  ⟨regs, fun k => if h : k.val < 37 then
    (MatrixEntryProgram.typedInput p i u y xs (fun _ => false)).stacks ⟨k.val, h⟩
    else if k = 37 then List.replicate j true
    else if k = 42 then List.replicate n true
    else if k = 43 then out
    else if k = 46 then constant
    else if k = 47 then shape else []⟩

def entryAllowance : ℕ :=
  ∑ t : Fin Q, MatrixExtendedEntryProgram.programBudget p i t u y xs

def coefficientAllowance : ℕ :=
  entryAllowance p i u y xs + 6010 * (width p + 1)^2 + 44 * width p + 8

def valueAt (j : ℕ) : ZMod p :=
  if h : j < Q then MatrixExtendedEntryProgram.value p i ⟨j, h⟩ u y xs else 0

def bytesAt (j : ℕ) : Word := CorrectionScalarCanonical.quartet p (-valueAt p i u y xs j)

def vector (j n : ℕ) : Word := ((List.range' j n).map (bytesAt p i u y xs)).flatten

@[simp] theorem bytesAt_length (j : ℕ) : (bytesAt p i u y xs j).length = 4 * width p :=
  CorrectionScalarCanonical.quartet_length _ _

@[simp] theorem vector_length (j n : ℕ) : (vector p i u y xs j n).length = n * (4 * width p) := by
  induction n generalizing j with
  | zero => simp [vector]
  | succ n ih =>
      simp only [vector, List.range'_succ, List.map_cons, List.flatten_cons, List.length_append]
      rw [bytesAt_length, show (((List.range' (j + 1) n).map (bytesAt p i u y xs)).flatten).length =
        n * (4 * width p) from ih (j + 1)]
      ring

theorem vector_succ (j n : ℕ) :
    vector p i u y xs j (n + 1) = bytesAt p i u y xs j ++ vector p i u y xs (j + 1) n := by
  simp [vector, List.range'_succ]

theorem entry_eval (h2 : (2 : ZMod p) ≠ 0) (t : Fin Q)
    (constant shape : Word) (regs : Fin 10 → Bool) (n : ℕ) (out : Word) :
    ∃ steps ≤ MatrixExtendedEntryProgram.programBudget p i t u y xs, ∃ rf,
      Eval entry steps (state p i u y xs constant shape regs t.val n out)
        ⟨rf, Function.update (state p i u y xs constant shape regs t.val n out).stacks 0
          (word p (MatrixExtendedEntryProgram.value p i t u y xs))⟩ := by
  let a := state p i u y xs constant shape regs t.val n out
  let first := MatrixExtendedEntryProgram.typedInput p i t u y xs regs
  obtain ⟨rf, steps, hsteps, ht⟩ := MatrixExtendedEntryProgram.program_runsIn p h2 i t u y xs regs
  have hs : ∀ k : Fin 42, a.stacks (entryMap k) = first.stacks k := by
    intro k
    fin_cases k <;> rfl
  have hin : embedState id entryMap a first = a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id entryMap_injective
    · intros; rfl
    · intro k hk; exact False.elim (hk ⟨k, rfl⟩)
    · intro k; exact hs k
    · intros; rfl
  have hout : embedState id entryMap a
      (MatrixExtendedEntryProgram.output first rf
        (word p (MatrixExtendedEntryProgram.value p i t u y xs))) =
      (⟨rf, Function.update a.stacks 0
        (word p (MatrixExtendedEntryProgram.value p i t u y xs))⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id entryMap_injective
    · intros; rfl
    · intro k hk; exact False.elim (hk ⟨k, rfl⟩)
    · intro k
      by_cases hk : k = 0
      · subst k; simp [entryMap, MatrixExtendedEntryProgram.output]
      · have hk' : entryMap k ≠ 0 := by
          intro h; exact hk (entryMap_injective h)
        simp [MatrixExtendedEntryProgram.output, hk, hk', hs]
    · intro k hk
      have h0 : k ≠ 0 := fun h => hk ⟨0, h.symm⟩
      simp [h0]
  have he := eval_call_lifted MatrixExtendedEntryProgram.program id entryMap a
    Function.injective_id entryMap_injective (a := first)
    (b := MatrixExtendedEntryProgram.output first rf
      (word p (MatrixExtendedEntryProgram.value p i t u y xs))) ht
  exact ⟨steps, hsteps, rf, by simpa only [entry, hin, hout] using he⟩

theorem coefficient_eval (h2 : (2 : ZMod p) ≠ 0) (j n : ℕ) (hj : j < Q)
    (constant shape : Word) (regs : Fin 10 → Bool) (out : Word)
    (hcw : constant.length = width p) (hcv : BinaryArithmetic.toNat constant = p - 1)
    (hsw : shape.length = 4 * width p) :
    ∃ steps ≤ coefficientAllowance p i u y xs, ∃ rf,
      Eval coefficient steps (state p i u y xs constant shape regs j n out)
        (state p i u y xs constant shape rf j n ((bytesAt p i u y xs j).reverse ++ out)) := by
  let t : Fin Q := ⟨j, hj⟩
  let a := state p i u y xs constant shape regs j n out
  obtain ⟨ne, hne, re, he⟩ := entry_eval p i u y xs h2 t constant shape regs n out
  let mid : Data := ⟨re, Function.update a.stacks 0
    (word p (MatrixExtendedEntryProgram.value p i t u y xs))⟩
  obtain ⟨ns, hns, b, hscalar, hb⟩ := CorrectionScalarCanonical.command_eval p
    (MatrixExtendedEntryProgram.value p i t u y xs) constant shape mid
    (by simp [mid])
    (by simp +decide [mid, a, state, MatrixEntryProgram.typedInput, MatrixEntryProgram.input])
    (by simp +decide [mid, a, state])
    (by simp +decide [mid, a, state])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals rfl)
    hcw hcv hsw
  have hb' : b = state p i u y xs constant shape b.regs j n
      ((bytesAt p i u y xs j).reverse ++ out) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hb]
    funext k
    by_cases hk0 : k = 0
    · subst k
      simp +decide [mid, a, state, MatrixEntryProgram.typedInput, MatrixEntryProgram.input]
    · by_cases hk43 : k = 43
      · subst k
        simp +decide [mid, a, state, bytesAt, valueAt, hj, t]
      · simp +decide [mid, a, state, hk0, hk43]
  rw [hb'] at hscalar
  have hentry : MatrixExtendedEntryProgram.programBudget p i t u y xs ≤ entryAllowance p i u y xs := by
    change MatrixExtendedEntryProgram.programBudget p i t u y xs ≤
      ∑ s : Fin Q, MatrixExtendedEntryProgram.programBudget p i s u y xs
    exact Finset.single_le_sum
      (f := fun s : Fin Q => MatrixExtendedEntryProgram.programBudget p i s u y xs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  exact ⟨ne + ns, by dsimp [coefficientAllowance]; omega, b.regs, he.seq hscalar⟩

def testedRegs (regs : Fin 10 → Bool) (n : ℕ) : Fin 10 → Bool :=
  readRegs regs 8 9 (List.replicate n true).head?

theorem tested_active (regs : Fin 10 → Bool) (n : ℕ) :
    testedRegs regs n 9 = decide (n ≠ 0) := by
  cases n <;> simp [testedRegs, readRegs, List.replicate_succ]

theorem peek_eval (constant shape : Word) (regs : Fin 10 → Bool) (j n : ℕ) (out : Word) :
    Eval peek 1 (state p i u y xs constant shape regs j n out)
      (state p i u y xs constant shape (testedRegs regs n) j n out) := by
  exact .base (.atom _ _)

theorem pop_eval (constant shape : Word) (regs : Fin 10 → Bool) (j n : ℕ) (out : Word) :
    Eval pop 1 (state p i u y xs constant shape regs j (n + 1) out)
      (state p i u y xs constant shape (readRegs regs 8 9 (some true)) j n out) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop (42 : Fin 49) 8 9)
    (state p i u y xs constant shape regs j (n + 1) out))
  convert h using 1
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk
    · simp +decide [state, StructuredProgram.Atom.instr,
 execInstr, List.replicate_succ
]
    · funext k
      by_cases hk : k = 42
      · subst k
        simp +decide [state, StructuredProgram.Atom.instr,
 execInstr,
          List.replicate_succ]
      · simp +decide [state, hk, StructuredProgram.Atom.instr,
 execInstr]

theorem advance_eval (constant shape : Word) (regs : Fin 10 → Bool) (j n : ℕ) (out : Word) :
    Eval advance 2 (state p i u y xs constant shape regs j n out)
      (state p i u y xs constant shape (Function.update regs 0 true) (j + 1) n out) := by
  have h := TupleProgram.pushConst_eval (37 : Fin 49) (0 : Fin 10) true
    (state p i u y xs constant shape regs j n out)
  convert h using 1
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk rfl
    funext k
    by_cases hk : k = 37
    · subst k; simp +decide [state, List.replicate_succ]
    · simp +decide [state, hk]

end SubexponentialSAT.Subexp.CorrectionVectorProgram

end OAI.Algorithms
