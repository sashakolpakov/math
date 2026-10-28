import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainController
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawRuntime

namespace OAI.Algorithms

/-!
# Closing the measured controller bound

These lemmas use the actual controller's boot and record budget. They charge
every encoded record even if the machine returns early. The remaining
premises are numerical bounds on those same executions and records.
-/

namespace SubexponentialSAT.SubexpMainCostAssembly

open SubexpComputation

theorem record_budget_le (records : List (List Bool)) (cost : List Bool → ℕ)
    (P : ℝ) (h : ∀ bits ∈ records,
      ((6 * bits.length + cost bits + 7 : ℕ) : ℝ) ≤ P) :
    (RecordPrograms.budget cost records : ℝ) ≤ (records.length : ℝ) * P := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons bits rest ih =>
      have hh := h bits (by simp)
      have ht := ih (fun b hb => h b (by simp [hb]))
      simpa only [RecordPrograms.budget, List.length_cons, Nat.cast_add,
        Nat.cast_one, add_mul, one_mul, add_comm] using add_le_add hh ht

theorem measured_bound (boot : ℕ) (records : List (List Bool)) (cost : List Bool → ℕ)
    {P : ℝ} (hP : 1 ≤ P) (hb : (boot : ℝ) ≤ P) (hn : (records.length : ℝ) ≤ P)
    (hl : ∀ bits ∈ records, ((6 * bits.length + cost bits + 7 : ℕ) : ℝ) ≤ P) :
    ((boot + 5 + RecordPrograms.budget cost records : ℕ) : ℝ) ≤ 7 * P ^ 2 := by
  have hP0 : 0 ≤ P := le_trans (by norm_num) hP
  have hr := (record_budget_le records cost P hl).trans
    (mul_le_mul_of_nonneg_right hn hP0)
  have hs : ((boot + 5 + RecordPrograms.budget cost records : ℕ) : ℝ) ≤ P + 5 + P * P := by
    push_cast
    linarith
  nlinarith [sq_nonneg (P - 1)]

/-- A single uniform envelope for the measured startup, number of records,
and each complete record visit closes the source-machine runtime estimate. -/
theorem measured_envelope (boot : ℕ) (records : List (List Bool)) (cost : List Bool → ℕ)
    {C a : ℝ} {d L n : ℕ} (hC : 1 ≤ C) (ha : 0 ≤ a)
    (hb : (boot : ℝ) ≤ runtimeBound C a d L n)
    (hn : (records.length : ℝ) ≤ runtimeBound C a d L n)
    (hl : ∀ bits ∈ records, ((6 * bits.length + cost bits + 7 : ℕ) : ℝ) ≤
      runtimeBound C a d L n) :
    ((boot + 5 + RecordPrograms.budget cost records : ℕ) : ℝ) ≤
      runtimeBound (7 * C ^ 2) (2 * a) (d * 2) L n := by
  calc
    _ ≤ 7 * runtimeBound C a d L n ^ 2 :=
      measured_bound boot records cost (one_le_runtimeBound hC ha d L n) hb hn hl
    _ = _ := by rw [runtimeBound_pow, ← runtimeBound_mul_constant]; norm_num

theorem canonical_execution {er es n : ℕ} {p : SubexpMainProgram.Phases er es}
    {leaf : SubexpMainProgram.MainCmd er es} {F : SAT.CNF (Fin n)}
    (run : SubexpMainController.Execution p leaf F)
    {C a : ℝ} {d : ℕ} (hC : 1 ≤ C) (ha : 0 ≤ a)
    (hb : ((run.prefixSteps + run.boot.setupSteps + run.boot.sparsifySteps : ℕ) : ℝ) ≤
      runtimeBound C a d (Encoding.formulaBitLength F) n)
    (hn : (run.records.length : ℝ) ≤ runtimeBound C a d (Encoding.formulaBitLength F) n)
    (hl : ∀ bits ∈ run.records, ((6 * bits.length + run.cost bits + 7 : ℕ) : ℝ) ≤
      runtimeBound C a d (Encoding.formulaBitLength F) n) :
    (run.bound : ℝ) ≤ runtimeBound (7 * C ^ 2) (2 * a) (d * 2)
      (Encoding.formulaBitLength F) n :=
  measured_envelope _ run.records run.cost hC ha hb hn hl

theorem ordered_execution {er es n : ℕ} {p : SubexpMainProgram.Phases er es}
    {leaf : SubexpMainProgram.MainCmd er es} {F : SubexpOrderedRawPrefix.Formula n}
    (run : SubexpOrderedRawRuntime.Execution p leaf F)
    {C a : ℝ} {d : ℕ} (hC : 1 ≤ C) (ha : 0 ≤ a)
    (hb : ((run.prefixSteps + run.boot.setupSteps + run.boot.sparsifySteps : ℕ) : ℝ) ≤
      runtimeBound C a d (SubexpOrderedRawPrefix.bitLength F) n)
    (hn : (run.records.length : ℝ) ≤ runtimeBound C a d (SubexpOrderedRawPrefix.bitLength F) n)
    (hl : ∀ bits ∈ run.records, ((6 * bits.length + run.cost bits + 7 : ℕ) : ℝ) ≤
      runtimeBound C a d (SubexpOrderedRawPrefix.bitLength F) n) :
    (run.bound : ℝ) ≤ runtimeBound (7 * C ^ 2) (2 * a) (d * 2)
      (SubexpOrderedRawPrefix.bitLength F) n :=
  measured_envelope _ run.records run.cost hC ha hb hn hl

end SubexponentialSAT.SubexpMainCostAssembly

end OAI.Algorithms
