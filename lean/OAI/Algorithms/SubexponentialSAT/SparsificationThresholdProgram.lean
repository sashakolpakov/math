import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionProgram
import OAI.Algorithms.SubexponentialSAT.SparsificationBudget

namespace OAI.Algorithms

/-!
# Fixed arithmetic expressions for the sparsification thresholds

The clause width is fixed before the input is read. Thus the recurrence is
compiled to a finite arithmetic expression; its variables are encoded word
data. No expression size or control table depends on M or the inverse budget.
-/

namespace SubexponentialSAT.SparsificationThresholdProgram

open ArithmeticExpressionProgram

/-- A fixed exponent is compiled by finite repetition of multiplication. -/
def powerExpr (e : Expr) : ℕ → Expr
  | 0 => .const 1
  | j + 1 => .mul (powerExpr e j) e

theorem eval_powerExpr (M : ℕ) (e : Expr) (j : ℕ) :
    eval M (powerExpr e j) = eval M e ^ j := by
  induction j with
  | zero => simp [powerExpr, eval]
  | succ j ih => simp [powerExpr, eval, ih, pow_succ]

/-- The cumulative insertion constants, expressed using one input word M. -/
def cumulativeExpr : ℕ → Expr
  | 0 => .const 0
  | 1 => .const 4
  | j + 2 =>
      let previous := cumulativeExpr (j + 1)
      .add previous
        (.mul
          (.add
            (.mul (.const (j + 1).factorial)
              (powerExpr (.pred (.mul .input previous)) (j + 1)))
            (.const 1))
          (.add (.const 2) previous))

theorem eval_cumulativeExpr (M : ℕ) : ∀ j,
    eval M (cumulativeExpr j) = SparsificationConstants.C M j
  | 0 => rfl
  | 1 => rfl
  | j + 2 => by
      simp only [cumulativeExpr, eval, eval_powerExpr,
        eval_cumulativeExpr M (j + 1), SparsificationConstants.C]

/-- The per-literal degree cap at one width, including the unit-width case. -/
def degreeExpr : ℕ → Expr
  | 0 => .const 0
  | 1 => .const 1
  | j + 2 =>
      .mul (.const (j + 1).factorial)
        (powerExpr (.pred (.mul .input (cumulativeExpr (j + 1)))) (j + 1))

theorem eval_degreeExpr (M j : ℕ) :
    eval M (degreeExpr j) = SparsificationConstants.L M j := by
  cases j with
  | zero => rfl
  | succ j =>
      cases j with
      | zero => rfl
      | succ j =>
          simp only [degreeExpr, eval, eval_powerExpr, eval_cumulativeExpr,
            SparsificationConstants.L]

def thresholdExpr (d : ℕ) : Expr := .mul .input (cumulativeExpr (d - 1))

theorem eval_thresholdExpr (M d : ℕ) :
    eval M (thresholdExpr d) = SparsificationConstants.z M d := by
  simp only [thresholdExpr, eval, eval_cumulativeExpr, SparsificationConstants.z]

/-- The complete occurrence bound B=2*sum L_j. -/
def occurrenceExpr : ℕ → Expr
  | 0 => .const 0
  | k + 1 => .add (occurrenceExpr k) (.mul (.const 2) (degreeExpr (k + 1)))

theorem eval_occurrenceExpr (M k : ℕ) :
    eval M (occurrenceExpr k) = SparsificationConstants.occurrenceCap M k := by
  induction k with
  | zero => simp [occurrenceExpr, eval]
  | succ k ih =>
      simp only [occurrenceExpr, eval, ih, eval_degreeExpr,
        SparsificationConstants.occurrenceCap_succ]

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- A fixed expression is compiled into a fixed finite Boolean program. -/
def programFor (e : Expr) :=
  compiled (command e)
    (inputPort (by have := slots_ge e; omega))
    (outputPort (by have := slots_ge e; omega))

/-- The original input remains available; the output and scratch layout is
exact, and both cost and raw output length are bounded for padded inputs. -/
theorem programFor_correct (e : Expr) (xs : List Bool) (regs : Fin 8 → Bool) :
    ∃ word rf,
      RunsIn (programFor e) ((timeCoeff e + 1) * (xs.length + 1)^2)
        ((state (by have := slots_ge e; omega) regs xs []).withPC
          (some (programFor e).entry))
        ((state (by have := slots_ge e; omega) rf xs word).withPC none) ∧
      BinaryArithmetic.toNat word = eval (BinaryArithmetic.toNat xs) e ∧
      word.length ≤ widthCoeff e * (xs.length + 1) := by
  obtain ⟨n, word, rf, hrun, hvalue, hwidth, htime⟩ := command_spec e xs regs
  refine ⟨word, rf, ⟨n + 1, ?_, ?_⟩, hvalue, hwidth⟩
  · have hsq : 1 ≤ (xs.length + 1)^2 := by nlinarith
    nlinarith
  · exact compiled_halt_trace hrun _ _

def cumulativeProgram (j : ℕ) := programFor (cumulativeExpr j)
def degreeProgram (j : ℕ) := programFor (degreeExpr j)
def thresholdProgram (d : ℕ) := programFor (thresholdExpr d)
def occurrenceProgram (k : ℕ) := programFor (occurrenceExpr k)

theorem cumulativeProgram_correct (j : ℕ) (xs : List Bool) (regs : Fin 8 → Bool) :
    ∃ word rf,
      RunsIn (cumulativeProgram j)
        ((timeCoeff (cumulativeExpr j) + 1) * (xs.length + 1)^2)
        ((state (by have := slots_ge (cumulativeExpr j); omega) regs xs []).withPC
          (some (cumulativeProgram j).entry))
        ((state (by have := slots_ge (cumulativeExpr j); omega) rf xs word).withPC none) ∧
      BinaryArithmetic.toNat word = SparsificationConstants.C (BinaryArithmetic.toNat xs) j ∧
      word.length ≤ widthCoeff (cumulativeExpr j) * (xs.length + 1) := by
  simpa only [cumulativeProgram, eval_cumulativeExpr] using
    programFor_correct (cumulativeExpr j) xs regs

theorem degreeProgram_correct (j : ℕ) (xs : List Bool) (regs : Fin 8 → Bool) :
    ∃ word rf,
      RunsIn (degreeProgram j)
        ((timeCoeff (degreeExpr j) + 1) * (xs.length + 1)^2)
        ((state (by have := slots_ge (degreeExpr j); omega) regs xs []).withPC
          (some (degreeProgram j).entry))
        ((state (by have := slots_ge (degreeExpr j); omega) rf xs word).withPC none) ∧
      BinaryArithmetic.toNat word = SparsificationConstants.L (BinaryArithmetic.toNat xs) j ∧
      word.length ≤ widthCoeff (degreeExpr j) * (xs.length + 1) := by
  simpa only [degreeProgram, eval_degreeExpr] using
    programFor_correct (degreeExpr j) xs regs

theorem thresholdProgram_correct (d : ℕ) (xs : List Bool) (regs : Fin 8 → Bool) :
    ∃ word rf,
      RunsIn (thresholdProgram d)
        ((timeCoeff (thresholdExpr d) + 1) * (xs.length + 1)^2)
        ((state (by have := slots_ge (thresholdExpr d); omega) regs xs []).withPC
          (some (thresholdProgram d).entry))
        ((state (by have := slots_ge (thresholdExpr d); omega) rf xs word).withPC none) ∧
      BinaryArithmetic.toNat word = SparsificationConstants.z (BinaryArithmetic.toNat xs) d ∧
      word.length ≤ widthCoeff (thresholdExpr d) * (xs.length + 1) := by
  simpa only [thresholdProgram, eval_thresholdExpr] using
    programFor_correct (thresholdExpr d) xs regs

theorem occurrenceProgram_correct (k : ℕ) (xs : List Bool) (regs : Fin 8 → Bool) :
    ∃ word rf,
      RunsIn (occurrenceProgram k)
        ((timeCoeff (occurrenceExpr k) + 1) * (xs.length + 1)^2)
        ((state (by have := slots_ge (occurrenceExpr k); omega) regs xs []).withPC
          (some (occurrenceProgram k).entry))
        ((state (by have := slots_ge (occurrenceExpr k); omega) rf xs word).withPC none) ∧
      BinaryArithmetic.toNat word =
        SparsificationConstants.occurrenceCap (BinaryArithmetic.toNat xs) k ∧
      word.length ≤ widthCoeff (occurrenceExpr k) * (xs.length + 1) := by
  simpa only [occurrenceProgram, eval_occurrenceExpr] using
    programFor_correct (occurrenceExpr k) xs regs

end SubexponentialSAT.SparsificationThresholdProgram

end OAI.Algorithms
