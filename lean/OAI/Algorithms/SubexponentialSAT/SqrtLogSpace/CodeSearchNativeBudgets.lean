import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets

/-! Numerical bounds for the actual graph-then-local code stage, including
all physical routing, saved outputs, and reused-bank cleanup. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets
open SqrtLog SparseCodeSearch CodeSearchBudgets

/-- Unary entry metadata already pays for both retained matrix dimensions. -/
theorem searchBoundary_le (A m B : ℕ)
    (hg : SparseCode.degree m B * SparseCode.dimension m B ≤ A)
    (hl : SparseCode.localRows m B * SparseCode.degree m B ≤ A) :
    NativeCode.graphBoundary A m B ≤ 7 * A + 1 ∧
    NativeCode.searchBoundary A m B ≤ 13 * A + 2 := by
  simp only [NativeCode.graphBoundary, NativeCode.searchBoundary, boundary]
  omega

/-- The actual graph/local sequence has a quadratic source-prefix bound
when its exact input metadata words fit in the supplied input bound. -/
theorem searchesSpace_le (A m B ql Dl : ℕ) (hA : 1 ≤ A)
    (hD : SparseCode.degree m B ≤ A)
    (ht : SparseCode.localRows m B ≤ A)
    (hd : SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ A)
    (hr : SparseCode.dimension m B ≤ A) (hq : ql ≤ A) (hDl : Dl ≤ A)
    (hg : SparseCode.degree m B * SparseCode.dimension m B ≤ A)
    (hl : SparseCode.localRows m B * SparseCode.degree m B ≤ A) :
    NativeCode.searchesSpace A m B ql Dl ≤ 20000000000000000 * A ^ 2 := by
  have hb := searchBoundary_le A m B hg hl
  have hgb : NativeCode.graphBoundary A m B ≤ 8 * A := by omega
  have hsb : NativeCode.searchBoundary A m B ≤ 15 * A := by omega
  have hgg := graphCodeSpace_polynomial A (SparseCode.degree m B)
    (SparseCode.dimension m B) ql Dl
  have hll := localCodeSpace_polynomial (NativeCode.graphBoundary A m B)
    (SparseCode.localRows m B) (SparseCode.degree m B)
    (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1)
  have hgs : A + SparseCode.degree m B + SparseCode.dimension m B + ql + Dl + 1 ≤ 6 * A := by omega
  have hls : NativeCode.graphBoundary A m B + SparseCode.localRows m B +
      SparseCode.degree m B + (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1) + 1 ≤
      12 * A := by omega
  have hgg' := hgg.trans (Nat.mul_le_mul_left 100000000000000 (Nat.pow_le_pow_left hgs 2))
  have hll' := hll.trans (Nat.mul_le_mul_left 100000000000000 (Nat.pow_le_pow_left hls 2))
  have hp : A ≤ A ^ 2 := by nlinarith only [hA]
  have hgg'' : graphSpace A (SparseCode.degree m B) (SparseCode.dimension m B) ql Dl ≤
      20000000000000000 * A ^ 2 := by nlinarith only [hgg']
  have hll'' : localSpace (NativeCode.graphBoundary A m B) (SparseCode.localRows m B)
      (SparseCode.degree m B) (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1) ≤
      20000000000000000 * A ^ 2 := by nlinarith only [hll']
  have hbA : A ≤ 20000000000000000 * A ^ 2 := by nlinarith only [hp]
  have hbG : NativeCode.graphBoundary A m B ≤ 20000000000000000 * A ^ 2 := by nlinarith only [hgb, hp]
  have hbL : NativeCode.searchBoundary A m B ≤ 20000000000000000 * A ^ 2 := by nlinarith only [hsb, hp]
  unfold NativeCode.searchesSpace NativeCode.graphStageSpace NativeCode.localStageSpace
  exact max_le (max_le hbA (max_le (max_le hgg'' hbA) hbG))
    (max_le hbG (max_le (max_le hll'' hbG) hbL))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets
open SqrtLog SqrtLog.Asymptotic
open Filter
open scoped Topology

/-- The actual four code dimensions satisfy the original numerical height
estimate, uniformly over every leaf with the chosen occurrence cap. -/
theorem produced_dimensions_le (n m B q : ℕ) (hm : 0 < m) (hB : 0 < B)
    (hmn : m ≤ n * B) (hBn : B ≤ L n ^ q) :
    let H := (320000 * (q + 2) ^ 3 + q + 4) * L n ^ (2 * q + 3)
    SparseCode.localRows m B ≤ H ∧ SparseCode.degree m B ≤ H ∧
      SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H ∧
      SparseCode.dimension m B ≤ H := by
  have hd := (SparseCode.degree_le_bound m B).trans
    (CostAssembly.code_degreeBound_le n m B q hmn hBn)
  have hl := CostAssembly.code_logSize_le n m B q hmn hBn
  have hp : L n ≤ L n ^ (2 * q + 3) := by
    simpa using Nat.pow_le_pow_right (L_pos n) (by omega : 1 ≤ 2 * q + 3)
  have hpos : 1 ≤ L n ^ (2 * q + 3) := Nat.one_le_pow _ _ (L_pos n)
  have height : SparseCode.degree m B + SparseCode.logSize m + 2 ≤
      (320000 * (q + 2) ^ 3 + q + 4) * L n ^ (2 * q + 3) := by nlinarith
  have ht := Nat.div_le_self (SparseCode.degree m B) (8 * B)
  have hdist := Nat.div_le_self (SparseCode.degree m B) (100 * B * SparseCode.logSize m)
  have hr := SparseCode.dimension_lt_logSize hm hB
  dsimp only
  unfold SparseCode.localRows
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets
open SqrtLog SparseCodeSearch CodeSearchBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCost

/-- All actual routes, searches, retained outputs and clearing fit a fixed
cubic power of the original explicit numerical envelope. -/
theorem searchesTime_le_envelope (A m B ql Dl H W : ℕ)
    (ht : SparseCode.localRows m B ≤ H) (hD : SparseCode.degree m B ≤ H)
    (hd : SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H)
    (hr : SparseCode.dimension m B ≤ H) (hq : ql ≤ W) (hDl : Dl ≤ W)
    (hg : SparseCode.degree m B * SparseCode.dimension m B ≤ A)
    (hl : SparseCode.localRows m B * SparseCode.degree m B ≤ A) :
    NativeCode.searchesTime A m B ql Dl ≤
      5000000000 * (A + envelope 3000000000000 H W + 1) ^ 3 := by
  let t := SparseCode.localRows m B
  let D := SparseCode.degree m B
  let d := D / (100 * B * SparseCode.logSize m) + 1
  let r := SparseCode.dimension m B
  let E := envelope 3000000000000 H W
  let X := A + E + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hA : A ≤ X := by dsimp [X]; omega
  have hX3 : X ≤ X ^ 3 := by nlinarith [Nat.one_le_pow 2 X hX]
  have he := combinedNumeric_bound 0 0 0 0 t D d r ql Dl 1 1 H W
    3000000000000 ht hD hd hr hq hDl (by norm_num)
  simp only [one_mul] at he
  have hle : localNumeric 0 0 t D d (t * D) (3 ^ D) (3 ^ (t * D)) ≤ E := by dsimp [E]; omega
  have hge : graphNumeric 0 0 D r ql Dl (D * r) (2 ^ r) (2 ^ (D * r)) ≤ E := by dsimp [E]; omega
  have hb := searchBoundary_le A m B hg hl
  have hgb : NativeCode.graphBoundary A m B ≤ 8 * X := by omega
  have hL : NativeCode.graphBoundary A m B +
      localNumeric 0 0 t D d (t * D) (3 ^ D) (3 ^ (t * D)) + 1 ≤ 8 * X := by
    dsimp [X]
    omega
  have hG : A + graphNumeric 0 0 D r ql Dl (D * r) (2 ^ r) (2 ^ (D * r)) + 1 ≤ X := by
    dsimp [X]
    omega
  have hlt := (localCodeTime_le_numeric (NativeCode.graphBoundary A m B) 0 0 t D d).trans
    (Nat.mul_le_mul_left 8000000 (Nat.pow_le_pow_left hL 3))
  have hgt := (graphCodeTime_le_numeric A 0 0 D r ql Dl).trans
    (Nat.mul_le_mul_left 8000000 (Nat.pow_le_pow_left hG 3))
  have hbound : boundary (NativeCode.graphBoundary A m B) (t * D) ≤ 15 * X := by
    change NativeCode.searchBoundary A m B ≤ _
    omega
  change _ ≤ 5000000000 * X ^ 3
  unfold NativeCode.searchesTime NativeCode.graphStageTime NativeCode.localStageTime
  change 5 * (9 * A + 8) + 3 +
      (graphTime A D r ql Dl + 1 + (105 * NativeCode.graphBoundary A m B + 155)) +
      (4 * (9 * NativeCode.graphBoundary A m B + 8) + 3 +
        (localTime (NativeCode.graphBoundary A m B) t D d + 1 +
          (105 * boundary (NativeCode.graphBoundary A m B) (t * D) + 155))) ≤ _
  nlinarith only [hlt, hgt, hX, hX3, hA, hgb, hbound]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets
open SqrtLog SparseCodeSearch CodeSearchBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCost OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement
open Filter
open scoped Topology

/-- The complete native code stage preserves the supplied exponent scale;
its actual retained input bound remains an explicit fixed polynomial factor. -/
theorem eventually_searchesTime (heightCoefficient heightDegree wordDegree : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ A m B ql Dl H : ℕ,
      SparseCode.localRows m B ≤ H → SparseCode.degree m B ≤ H →
      SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H →
      SparseCode.dimension m B ≤ H →
      H ≤ heightCoefficient * OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.L n ^ heightDegree →
      ql ≤ (n + 1) ^ wordDegree → Dl ≤ (n + 1) ^ wordDegree →
      SparseCode.degree m B * SparseCode.dimension m B ≤ A →
      SparseCode.localRows m B * SparseCode.degree m B ≤ A →
      (NativeCode.searchesTime A m B ql Dl : ℝ) ≤
        runtimeBound 40000000000 3 3 A n := by
  filter_upwards [eventually_envelope 3000000000000 heightCoefficient heightDegree wordDegree]
    with n hn A m B ql Dl H ht hD hd hr hH hq hDl hg hl
  have h := cubic_cost_runtimeBound (NativeCode.searchesTime A m B ql Dl) A
    (envelope 3000000000000 H (max ql Dl)) n 5000000000
    (searchesTime_le_envelope A m B ql Dl H (max ql Dl)
      ht hD hd hr (le_max_left _ _) (le_max_right _ _) hg hl)
    (hn H (max ql Dl) hH (max_le hq hDl))
  norm_num only [Nat.cast_ofNat] at h
  exact h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets
open SqrtLog SqrtLog.Asymptotic SqrtLog.Statement
open Filter
open scoped Topology

/-- Uniform runtime for the actual selected dimensions. The only remaining
size hypotheses are the sparse leaf count and physical entry-word bounds. -/
theorem eventually_produced_searchesTime (q wordDegree : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ A m B ql Dl : ℕ,
      0 < m → 0 < B → m ≤ n * B → B ≤ L n ^ q →
      ql ≤ (n + 1) ^ wordDegree → Dl ≤ (n + 1) ^ wordDegree →
      SparseCode.degree m B * SparseCode.dimension m B ≤ A →
      SparseCode.localRows m B * SparseCode.degree m B ≤ A →
      (NativeCode.searchesTime A m B ql Dl : ℝ) ≤
        runtimeBound 40000000000 3 3 A n := by
  filter_upwards [eventually_searchesTime (320000 * (q + 2) ^ 3 + q + 4)
    (2 * q + 3) wordDegree]
    with n hn A m B ql Dl hm hB hmn hBn hq hDl hg hl
  obtain ⟨ht, hD, hd, hr⟩ := produced_dimensions_le n m B q hm hB hmn hBn
  exact hn A m B ql Dl _ ht hD hd hr le_rfl hq hDl hg hl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets
