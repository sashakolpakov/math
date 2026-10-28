import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparsifyProgramVisits

namespace OAI.Algorithms

/-! The actual encoded sparsifier at the new schedule. Search instructions,
node setup, worklist updates and the primitive compiler are all charged.
This stage starts after input normalization and threshold-bank construction;
those separate executable phases supply `FrameReady`, `BankValues` and
`BankLengths`. No equality with an independently selected splitter is used. -/
namespace SubexponentialSAT.SqrtLog.SparsifyProgram

open Filter BitProgram
open ExecSparsifyObserved ExecSparsifyBoundary
open ExecSparsifyNode (Data)
open SparsificationConstants SparsificationBudgetProgram
open Asymptotic

/-- Source instruction cost of the fixed encoded program. -/
theorem eventually_runCost_target (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∀ᶠ n : ℕ in atTop, ∀ (frame : Data k) (hf : FrameReady frame)
      (hb : BankValues (arity T n) frame), BankLengths k T n frame →
      ∀ F : Formula n, Ready k F →
      SunflowerBranch.Antichain (ExecCNF.formulaSet F) →
      (ExecEncodedSparsifier.runCost frame (arity T n) hf hb (arity_ge_two k T n) F : ℝ) ≤
        11 * (2 : ℝ) ^ (130 * Statement.runtimeScale n) := by
  obtain ⟨q, hq⟩ := eventually_node_work_le_power k T
  have hw := Asymptotic.eventually_variable_search_target
    (fun n => (s n + 2) ^ q) q (C := 1) (by norm_num)
    (Filter.Eventually.of_forall (fun n => by simp))
  filter_upwards [hq, hw, eventually_visits_target k T hk hT] with n hn hW hV
  intro frame hf hb hl F hF hanti
  let W := (n + 1) ^ ((s n + 2) ^ q)
  have hnode : ∀ G : Formula n, Ready k G →
      ExecSparsifyExecution.cost frame (arity T n) hf hb (arity_ge_two k T n) G +
        ExecWorklistLoop.updateCost encode G
          ((branching frame (arity T n) hf hb (arity_ge_two k T n)).split G) ≤ W := by
    intro G hG
    have h := hn frame hf hb hl G hG
    change _ + _ + 3 ≤ W at h
    change ExecSparsifyExecution.cost frame (arity T n) hf hb (arity_ge_two k T n) G +
      ExecWorklistLoop.updateCost encode G
        (split frame (arity T n) hf hb (arity_ge_two k T n) G) ≤ W
    omega
  have hc := ExecEncodedSparsifier.runCost_le_visits frame (arity T n) hf hb
    (arity_ge_two k T n) F hF W hnode
  have hv := hV frame hf hb F hF hanti
  let X : ℝ := (2 : ℝ) ^ Statement.runtimeScale n
  let Y : ℝ := (2 : ℝ) ^ (129 * Statement.runtimeScale n)
  have hx : 1 ≤ X := Real.one_le_rpow (by norm_num) (Statement.runtimeScale_nonneg n)
  have hy : 1 ≤ Y := Real.one_le_rpow (by norm_num) (by
    have := Statement.runtimeScale_nonneg n; positivity)
  have hW' : (W : ℝ) ≤ X := hW
  have hc' : (ExecEncodedSparsifier.runCost frame (arity T n) hf hb
      (arity_ge_two k T n) F : ℝ) ≤
      ((W : ℝ) + 4) * ((ExecSparsifyWorklist.run
        (branching frame (arity T n) hf hb (arity_ge_two k T n))
        (ExecSparsifyWorklist.initial F)).visits : ℝ) + 6 := by exact_mod_cast hc
  have hbnd : ((W : ℝ) + 4) * ((ExecSparsifyWorklist.run
      (branching frame (arity T n) hf hb (arity_ge_two k T n))
      (ExecSparsifyWorklist.initial F)).visits : ℝ) + 6 ≤ 11 * (X * Y) := by
    have hp := mul_le_mul (show (W : ℝ) + 4 ≤ 5 * X by linarith) hv
      (Nat.cast_nonneg _) (by linarith : 0 ≤ 5 * X)
    have hxy : 1 ≤ X * Y := one_le_mul_of_one_le_of_one_le hx hy
    nlinarith
  have heq : X * Y = (2 : ℝ) ^ (130 * Statement.runtimeScale n) := by
    dsimp [X, Y]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  exact (hc'.trans hbnd).trans_eq (by rw [heq])

private theorem nat_mul_bound (C m : ℕ) (x : ℝ)
    (h : (m : ℝ) ≤ 11 * x) :
    ((C * m : ℕ) : ℝ) ≤ (11 * C : ℕ) * x := by
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    (C : ℝ) * (m : ℝ) ≤ (C : ℝ) * (11 * x) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α := ℝ) C)
    _ = 11 * (C : ℝ) * x := by ring

/-- Primitive instruction overhead is a fixed constant depending only on k. -/
theorem eventually_primitiveCost_target (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∀ᶠ n : ℕ in atTop, ∀ (frame : Data k) (hf : FrameReady frame)
      (hb : BankValues (arity T n) frame), BankLengths k T n frame →
      ∀ F : Formula n, Ready k F →
      SunflowerBranch.Antichain (ExecCNF.formulaSet F) →
      ((primitiveOverhead (ExecEncodedSparsifier.program k) *
        ExecEncodedSparsifier.runCost frame (arity T n) hf hb
          (arity_ge_two k T n) F : ℕ) : ℝ) ≤
        (11 * primitiveOverhead (ExecEncodedSparsifier.program k) : ℕ) *
          (2 : ℝ) ^ (130 * Statement.runtimeScale n) := by
  filter_upwards [eventually_runCost_target k T hk hT] with n hn
  intro frame hf hb hl F hF hanti
  exact nat_mul_bound _ _ _ (hn frame hf hb hl F hF hanti)

/-- This is the actual source trace and the model-preserving leaf output
used by the controller before one final primitive compilation. -/
theorem program_sparsifies {n k T : ℕ} (frame : Data k)
    (hf : FrameReady frame) (hb : BankValues (arity T n) frame)
    (F : Formula n) (hF : Ready k F) :
    RunsIn (ExecEncodedSparsifier.program k)
      (ExecEncodedSparsifier.runCost frame (arity T n) hf hb (arity_ge_two k T n) F)
      ((ExecEncodedSparsifier.initialState frame F).withPC
        (some (ExecEncodedSparsifier.program k).entry))
      ((ExecEncodedSparsifier.finalState frame
        (leaves frame (arity T n) hf hb (arity_ge_two k T n) F)).withPC none) ∧
    ExecEncodedSparsifier.CorrectOutput k
      (SparsifyDyadic.occurrenceBound k T (s n)) F
      (leaves frame (arity T n) hf hb (arity_ge_two k T n) F) :=
  ExecEncodedSparsifier.program_sparsifies frame (dyadicM T (s n)) hf hb
    (arity_ge_two k T n) F hF (dyadicM_ge_two T (s n))


/-- A bounded, genuine instruction trace and the corresponding actual
ordered output, packaged together for the controller. -/
theorem eventually_program_trace (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∀ᶠ n : ℕ in atTop, ∀ (frame : Data k) (hf : FrameReady frame)
      (hb : BankValues (arity T n) frame), BankLengths k T n frame →
      ∀ F : Formula n, Ready k F →
      SunflowerBranch.Antichain (ExecCNF.formulaSet F) →
      ∃ steps : ℕ,
        RunsIn (ExecEncodedSparsifier.program k) steps
          ((ExecEncodedSparsifier.initialState frame F).withPC
            (some (ExecEncodedSparsifier.program k).entry))
          ((ExecEncodedSparsifier.finalState frame
            (leaves frame (arity T n) hf hb (arity_ge_two k T n) F)).withPC none) ∧
        (steps : ℝ) ≤ 11 * (2 : ℝ) ^ (130 * Statement.runtimeScale n) ∧
        ExecEncodedSparsifier.CorrectOutput k
          (SparsifyDyadic.occurrenceBound k T (s n)) F
          (leaves frame (arity T n) hf hb (arity_ge_two k T n) F) := by
  filter_upwards [eventually_runCost_target k T hk hT] with n hn
  intro frame hf hb hl F hF hanti
  exact ⟨_, (program_sparsifies frame hf hb F hF).1,
    hn frame hf hb hl F hF hanti, (program_sparsifies frame hf hb F hF).2⟩

/-- The bound applies directly after the checked normalizer, regardless of
the original input's number of repeated clauses or literals. The cost of
that preceding normalization is intentionally not included here. -/
theorem eventually_normalized_runCost_target (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∀ᶠ n : ℕ in atTop, ∀ (frame : Data k) (hf : FrameReady frame)
      (hb : BankValues (arity T n) frame), BankLengths k T n frame →
      ∀ F : Formula n, ExecSunflowerSearch.RawWidthAtMost k F →
      (ExecEncodedSparsifier.runCost frame (arity T n) hf hb (arity_ge_two k T n)
        (ExecSparsifyWorklist.normalizedInput F) : ℝ) ≤
        11 * (2 : ℝ) ^ (130 * Statement.runtimeScale n) := by
  filter_upwards [eventually_runCost_target k T hk hT] with n hn
  intro frame hf hb hl F hF
  exact hn frame hf hb hl _ (ExecSparsifyStartup.normalizedInput_ready F k hF)
    (ExecSparsifyStartup.normalizedInput_antichain F)


/-- Explicit primitive execution, with the instruction bound and semantic
specification attached to the very same emitted source leaf stream. -/
theorem eventually_primitive_trace (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∀ᶠ n : ℕ in atTop, ∀ (frame : Data k) (hf : FrameReady frame)
      (hb : BankValues (arity T n) frame), BankLengths k T n frame →
      ∀ F : Formula n, Ready k F →
      SunflowerBranch.Antichain (ExecCNF.formulaSet F) →
      ∃ steps : ℕ,
        Computation.RunsIn (primitive (ExecEncodedSparsifier.program k)).step steps
          (primitiveCfg (ExecEncodedSparsifier.program k)
            ((ExecEncodedSparsifier.initialState frame F).withPC
              (some (ExecEncodedSparsifier.program k).entry)))
          (primitiveCfg (ExecEncodedSparsifier.program k)
            ((ExecEncodedSparsifier.finalState frame
              (leaves frame (arity T n) hf hb (arity_ge_two k T n) F)).withPC none)) ∧
        (steps : ℝ) ≤ (11 * primitiveOverhead (ExecEncodedSparsifier.program k) : ℕ) *
          (2 : ℝ) ^ (130 * Statement.runtimeScale n) ∧
        ExecEncodedSparsifier.CorrectOutput k
          (SparsifyDyadic.occurrenceBound k T (s n)) F
          (leaves frame (arity T n) hf hb (arity_ge_two k T n) F) := by
  filter_upwards [eventually_primitiveCost_target k T hk hT] with n hn
  intro frame hf hb hl F hF hanti
  exact ⟨_, ExecEncodedSparsifier.primitive_runs frame (arity T n) hf hb
    (arity_ge_two k T n) F hF, hn frame hf hb hl F hF hanti,
    (program_sparsifies frame hf hb F hF).2⟩

end SubexponentialSAT.SqrtLog.SparsifyProgram

end OAI.Algorithms
