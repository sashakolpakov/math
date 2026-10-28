import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.DyadicSparsifyNodeBounds
import OAI.Algorithms.SubexponentialSAT.ExecEncodedSparsifier
import OAI.Algorithms.SubexponentialSAT.SubexpRuntime

namespace OAI.Algorithms

/-!
# The actual encoded dyadic sparsifier's source runtime

The visit count concerns the branching observed in the concrete tuple-order
program. The local bound counts its actual finite instructions, including
both child constructors and the worklist update. No event counter from the
older sublist implementation is used here.

The bank premises describe the words produced by the preceding setup phase.
The initial antichain and ordered-list invariant are supplied by the actual
normalizer. Constants are chosen before the input size, frame, and formula.
-/

namespace SubexponentialSAT.ExecDyadicSparsifierRuntime

open Filter BitProgram
open ExecSparsifyObserved ExecSparsifyBoundary
open ExecSparsifyNode (Data)
open SubexpPackingParameters
open SparsificationConstants SparsificationBudgetProgram
open DyadicMaskedSearchBounds (arity)
open DyadicSparsifyNodeBounds (BankLengths arity_ge_two)

def visitPrefactor (k T s : ℕ) : ℕ :=
  (C (dyadicM T s) (k - 1) + 1) * (k + 1)

theorem visitPrefactor_polynomialBound (k T : ℕ) :
    PolynomialBound (visitPrefactor k T) :=
  ((dyadicC_polynomialBound T (k - 1)).add (polynomialBound_const 1)).mul
    (polynomialBound_const (k + 1))

/-- The actual observed run has the quantitative sunflower-tree bound. -/
theorem visits_polynomial (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∃ q : ℕ, ∀ n : ℕ, GoodInput n → ∀ (frame : Data k)
      (hf : FrameReady frame) (hb : BankValues (arity T n) frame)
      (F : Formula n), Ready k F → SunflowerBranch.Antichain (ExecCNF.formulaSet F) →
      ((ExecSparsifyWorklist.run (branching frame (arity T n) hf hb (arity_ge_two k T n))
        (ExecSparsifyWorklist.initial F)).visits : ℝ) ≤
          ((s n + 2) ^ q : ℕ) * ((n : ℝ) + 1) ^ 2 *
            (2 : ℝ) ^ ((n : ℝ) / s n) := by
  obtain ⟨q, hq⟩ := QuantitativeSparsify.polynomialBound_shift_power
    (visitPrefactor_polynomialBound k T)
  refine ⟨q, ?_⟩
  intro n hn frame hf hb F hF hanti
  have hs := goodInput_s_pos hn
  have hv := visits_quantitative frame (DyadicSchedule.M T n) hf hb
    (arity_ge_two k T n) F hF hanti (DyadicSchedule.M_ge_two T n) (by omega)
    (1 / (s n : ℝ)) (hT.ratio_le hk (s n) hs) (hT.logb_budget hk (s n) hs)
  have hp : (visitPrefactor k T (s n) : ℝ) ≤ ((s n + 2) ^ q : ℕ) := by
    exact_mod_cast hq (s n)
  calc
    _ ≤ (visitPrefactor k T (s n) : ℝ) * ((n : ℝ) + 1) ^ 2 *
        (2 : ℝ) ^ ((n : ℝ) / s n) := by
      change
        ((ExecSparsifyWorklist.run
          (branching frame (SparsificationConstants.z (DyadicSchedule.M T n)) hf hb
            (arity_ge_two k T n)) (ExecSparsifyWorklist.initial F)).visits : ℝ) ≤ _
      simpa only [visitPrefactor, DyadicSchedule.M, DyadicMaskedSearchBounds.arity,
        Nat.cast_mul, one_div,
        div_eq_mul_inv, one_mul, mul_comm (s n : ℝ)⁻¹ (n : ℝ), mul_assoc] using hv
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hp (sq_nonneg _)) (by positivity)

/-- A fixed polynomial in the original input length bounds the prefactor;
the exponent constant two comes from the actual reciprocal schedule. -/
theorem visits_bound (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∃ A d : ℕ, 0 < A ∧ ∀ n : ℕ, GoodInput n → ∀ (L : ℕ)
      (frame : Data k) (hf : FrameReady frame) (hb : BankValues (arity T n) frame)
      (F : Formula n), Ready k F → SunflowerBranch.Antichain (ExecCNF.formulaSet F) →
      n ≤ L →
      ((ExecSparsifyWorklist.run (branching frame (arity T n) hf hb (arity_ge_two k T n))
        (ExecSparsifyWorklist.initial F)).visits : ℝ) ≤
          SubexpComputation.runtimeBound (A : ℝ) 2 d L n := by
  obtain ⟨q, hq⟩ := visits_polynomial k T hk hT
  refine ⟨2 ^ q, q + 2, by positivity, ?_⟩
  intro n hn L frame hf hb F hF hanti hnL
  have hv := hq n hn frame hf hb F hF hanti
  have hsL : (s n : ℝ) ≤ L := by exact_mod_cast (s_le_n n).trans hnL
  have hs : (s n : ℝ) + 2 ≤ 2 * ((L : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have hnL' : (n : ℝ) + 1 ≤ (L : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hnL 1
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (s n : ℝ) + 2) hs q
  have hn2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) hnL' 2
  have hpoly : ((s n : ℝ) + 2) ^ q * ((n : ℝ) + 1) ^ 2 ≤
      (2 : ℝ) ^ q * ((L : ℝ) + 1) ^ (q + 2) := by
    calc
      _ ≤ (2 * ((L : ℝ) + 1)) ^ q * ((L : ℝ) + 1) ^ 2 :=
        mul_le_mul hp hn2 (by positivity) (by positivity)
      _ = _ := by rw [mul_pow, pow_add]; ring
  have hn16 : 16 ≤ n := by
    have hsn := s_le_n n
    unfold GoodInput at hn
    omega
  have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (SubexpExponentArithmetic.natLog2_ratio_le_twice_scale hn16)
  have hv' : ((ExecSparsifyWorklist.run
      (branching frame (arity T n) hf hb (arity_ge_two k T n))
      (ExecSparsifyWorklist.initial F)).visits : ℝ) ≤
      ((s n : ℝ) + 2) ^ q * ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ ((n : ℝ) / s n) := by
    exact_mod_cast hv
  unfold SubexpComputation.runtimeBound
  push_cast
  exact hv'.trans (mul_le_mul hpoly he (by positivity) (by positivity))

/-- The output list is the same list emitted by the actual encoded run. -/
theorem leaves_bound (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∃ A d : ℕ, 0 < A ∧ ∀ n : ℕ, GoodInput n → ∀ (L : ℕ)
      (frame : Data k) (hf : FrameReady frame) (hb : BankValues (arity T n) frame)
      (F : Formula n), Ready k F → SunflowerBranch.Antichain (ExecCNF.formulaSet F) →
      n ≤ L →
      ((leaves frame (arity T n) hf hb (arity_ge_two k T n) F).length : ℝ) ≤
        SubexpComputation.runtimeBound (A : ℝ) 2 d L n := by
  obtain ⟨A, d, hA, hv⟩ := visits_bound k T hk hT
  refine ⟨A, d, hA, ?_⟩
  intro n hn L frame hf hb F hF hanti hnL
  exact (Nat.cast_le.mpr (ExecSparsifyWorklist.initial_run_leaves_length_le_visits
    (branching frame (arity T n) hf hb (arity_ge_two k T n)) F)).trans
      (hv n hn L frame hf hb F hF hanti hnL)

/-- The final encoded leaf stream has a bound of the same form. Thus a
linear transfer of this stream is charged without rescanning growing
output prefixes during the traversal. -/
theorem encoded_leaves_bound (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∃ A d : ℕ, 0 < A ∧ ∀ n : ℕ, GoodInput n → ∀ (L : ℕ)
      (frame : Data k) (hf : FrameReady frame) (hb : BankValues (arity T n) frame)
      (F : Formula n), Ready k F → SunflowerBranch.Antichain (ExecCNF.formulaSet F) →
      n ≤ L →
      ((Encoding.encodeList encode
        (leaves frame (arity T n) hf hb (arity_ge_two k T n) F)).length : ℝ) ≤
        SubexpComputation.runtimeBound (A : ℝ) 2 d L n := by
  obtain ⟨A, d, hA, hleaves⟩ := leaves_bound k T hk hT
  let K := 8 * k + 5
  let e := 2 * k + 1
  refine ⟨(2 * K + 3) * A, d + e, by positivity, ?_⟩
  intro n hn L frame hf hb F hF hanti hnL
  let N := (leaves frame (arity T n) hf hb (arity_ge_two k T n) F).length
  let X := ((L : ℝ) + 1) ^ (d + e) * (2 : ℝ) ^ (2 * SubexpComputation.scale n)
  have hN : (N : ℝ) ≤ (A : ℝ) * ((L : ℝ) + 1) ^ d *
      (2 : ℝ) ^ (2 * SubexpComputation.scale n) :=
    hleaves n hn L frame hf hb F hF hanti hnL
  have hbase : (1 : ℝ) ≤ (L : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have hpow : (1 : ℝ) ≤ ((L : ℝ) + 1) ^ e := one_le_pow₀ hbase
  have hexp : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * SubexpComputation.scale n) :=
    Real.one_le_rpow (by norm_num)
      (mul_nonneg (by norm_num) (SubexpComputation.scale_nonneg n))
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hbase) hexp
  have hAX : 1 ≤ (A : ℝ) * X :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast (show 1 ≤ A by omega)) hX
  have hnL' : (n : ℝ) + 1 ≤ (L : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnL 1
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) hnL' e
  have hcoef : 2 * ((K : ℝ) * ((n : ℝ) + 1) ^ e) + 2 ≤
      (2 * (K : ℝ) + 2) * ((L : ℝ) + 1) ^ e := by
    nlinarith [Nat.cast_nonneg (α := ℝ) K]
  have hterm : (2 * ((K : ℝ) * ((n : ℝ) + 1) ^ e) + 2) * (N : ℝ) ≤
      (2 * (K : ℝ) + 2) * (A : ℝ) * X := by
    calc
      _ ≤ ((2 * (K : ℝ) + 2) * ((L : ℝ) + 1) ^ e) *
          ((A : ℝ) * ((L : ℝ) + 1) ^ d * (2 : ℝ) ^ (2 * SubexpComputation.scale n)) :=
        mul_le_mul hcoef hN (Nat.cast_nonneg N) (by positivity)
      _ = _ := by dsimp [X]; rw [pow_add]; ring
  have hraw : ((Encoding.encodeList encode
      (leaves frame (arity T n) hf hb (arity_ge_two k T n) F)).length : ℝ) ≤
      1 + (2 * ((K : ℝ) * ((n : ℝ) + 1) ^ e) + 2) * (N : ℝ) := by
    exact_mod_cast leaves_encoding_length frame (arity T n) hf hb
      (arity_ge_two k T n) F hF
  calc
    _ ≤ ((2 * (K : ℝ) + 3) * (A : ℝ)) * X := by nlinarith
    _ = SubexpComputation.runtimeBound (((2 * K + 3) * A : ℕ) : ℝ) 2 (d + e) L n := by
      dsimp [X, SubexpComputation.runtimeBound]
      push_cast
      ring

/-- Full concrete instruction cost, including worklist updates and both
cleanup paths. The preceding setup and normalization phases are separate. -/
theorem runCost_bound (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∃ A d : ℕ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, ∀ (L : ℕ)
      (frame : Data k) (hf : FrameReady frame) (hb : BankValues (arity T n) frame),
      BankLengths k T n frame → ∀ F : Formula n, Ready k F →
      SunflowerBranch.Antichain (ExecCNF.formulaSet F) → n ≤ L →
      ((ExecEncodedSparsifier.runCost frame (arity T n) hf hb (arity_ge_two k T n) F) : ℝ) ≤
        SubexpComputation.runtimeBound (A : ℝ) 3 d L n := by
  obtain ⟨q, hnodes⟩ := DyadicSparsifyNodeBounds.eventually_node_work_le_power k T
  obtain ⟨A, d, hA, hv⟩ := visits_bound k T hk hT
  have hdegree : ∀ᶠ n : ℕ in atTop,
      (((s n + 2) ^ q : ℕ) : ℝ) ≤ (1 : ℝ) * ((s n : ℝ) + 2) ^ q :=
    Eventually.of_forall (fun n => by simp)
  have hsearch := SubexpRuntime.eventually_variable_degree_search
    (fun n => (s n + 2) ^ q) q (by norm_num : (0 : ℝ) < 1) hdegree
  refine ⟨11 * A, d, by omega, ?_⟩
  filter_upwards [hnodes, hsearch, eventually_goodInput] with n hnodes hsearch hn
  intro L frame hf hb hl F hF hanti hnL
  let W := (n + 1) ^ ((s n + 2) ^ q)
  let V := (ExecSparsifyWorklist.run
    (branching frame (arity T n) hf hb (arity_ge_two k T n))
    (ExecSparsifyWorklist.initial F)).visits
  let E := SubexpComputation.runtimeBound (A : ℝ) 2 d L n
  let X := (2 : ℝ) ^ SubexpComputation.scale n
  have hnode : ∀ G : Formula n, Ready k G →
      ExecSparsifyExecution.cost frame (arity T n) hf hb (arity_ge_two k T n) G +
        ExecWorklistLoop.updateCost encode G
          ((branching frame (arity T n) hf hb (arity_ge_two k T n)).split G) ≤ W := by
    intro G hG
    have h := hnodes frame hf hb hl G hG
    change _ + _ + 3 ≤ W at h
    change ExecSparsifyExecution.cost frame (arity T n) hf hb (arity_ge_two k T n) G +
      ExecWorklistLoop.updateCost encode G
        (split frame (arity T n) hf hb (arity_ge_two k T n) G) ≤ W
    omega
  have hc := ExecEncodedSparsifier.runCost_le_visits frame (arity T n) hf hb
    (arity_ge_two k T n) F hF W hnode
  have hc' : ((ExecEncodedSparsifier.runCost frame (arity T n) hf hb
      (arity_ge_two k T n) F) : ℝ) ≤ ((W : ℝ) + 4) * (V : ℝ) + 6 := by
    exact_mod_cast hc
  have hV : (V : ℝ) ≤ E := hv n hn L frame hf hb F hF hanti hnL
  have hE : 1 ≤ E := SubexpComputation.one_le_runtimeBound
    (by exact_mod_cast (show 1 ≤ A by omega)) (by norm_num) d L n
  have hX : 1 ≤ X := Real.one_le_rpow (by norm_num) (SubexpComputation.scale_nonneg n)
  have hW : (W : ℝ) ≤ X := hsearch
  have hWE : ((W : ℝ) + 4) * (V : ℝ) ≤ (5 * X) * E :=
    mul_le_mul (by linarith) hV (Nat.cast_nonneg V) (by positivity)
  have hXE : 1 ≤ X * E := one_le_mul_of_one_le_of_one_le hX hE
  calc
    _ ≤ 11 * (X * E) := by nlinarith
    _ = SubexpComputation.runtimeBound ((11 * A : ℕ) : ℝ) 3 d L n := by
      dsimp [X, E, SubexpComputation.runtimeBound]
      push_cast
      calc
        _ = (11 * (A : ℝ)) * ((L : ℝ) + 1) ^ d *
            ((2 : ℝ) ^ SubexpComputation.scale n *
              (2 : ℝ) ^ (2 * SubexpComputation.scale n)) := by ring
        _ = _ := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 2
          ring

/-- The fixed source program has a genuine halting trace within the bound;
its endpoint contains precisely the ordered leaves bounded above. -/
theorem program_trace_bound (k T : ℕ) (hk : 2 ≤ k) (hT : Control k T) :
    ∃ A d : ℕ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, ∀ (L : ℕ)
      (frame : Data k) (hf : FrameReady frame) (hb : BankValues (arity T n) frame),
      BankLengths k T n frame → ∀ F : Formula n, Ready k F →
      SunflowerBranch.Antichain (ExecCNF.formulaSet F) → n ≤ L →
      ∃ t : ℕ, Trace (ExecEncodedSparsifier.program k) t
        ((ExecEncodedSparsifier.initialState frame F).withPC
          (some (ExecEncodedSparsifier.program k).entry))
        ((ExecEncodedSparsifier.finalState frame
          (leaves frame (arity T n) hf hb (arity_ge_two k T n) F)).withPC none) ∧
        (t : ℝ) ≤ SubexpComputation.runtimeBound (A : ℝ) 3 d L n := by
  obtain ⟨A, d, hA, hc⟩ := runCost_bound k T hk hT
  refine ⟨A, d, hA, hc.mono ?_⟩
  intro n hn L frame hf hb hl F hF hanti hnL
  obtain ⟨t, ht, htrace⟩ := ExecEncodedSparsifier.program_runs frame (arity T n)
    hf hb (arity_ge_two k T n) F hF
  exact ⟨t, htrace, (Nat.cast_le.mpr ht).trans (hn L frame hf hb hl F hF hanti hnL)⟩

end SubexponentialSAT.ExecDyadicSparsifierRuntime

end OAI.Algorithms
