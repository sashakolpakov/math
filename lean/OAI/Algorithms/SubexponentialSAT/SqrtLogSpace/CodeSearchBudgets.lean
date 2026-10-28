import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCostPolynomial

/-! Fixed-degree bounds for the actual streamed sparse-code search commands.
The time comparison uses the original complete numerical search envelope;
workspace is bounded separately by ordinary input words and dimensions. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets
open SparseCodeSearch CodeChecks

/-- Every candidate and every invalid two-bit word is charged. -/
theorem streamedCodeTime_le (A md wd callback : ℕ) :
    timeBudget md (boundary A md)
      (candidateBudget (boundary A md) md wd callback
        (4 ^ wd * (callback + 110 * wd + 36) + 3))
      (candidateSpace (boundary A md) md wd callback) ≤
      4000000 * (A + md + wd + callback + 1) * (4 ^ md * 4 ^ wd) := by
  let S := A + md + wd + callback + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hB : boundary A md ≤ 7 * S := by dsimp [boundary, S]; omega
  have hsum : boundary A md + md + wd + callback + 1 ≤ 8 * S := by
    dsimp [boundary, S]
    omega
  have hC := candidateSpace_le (boundary A md) md wd callback
  have hC' : candidateSpace (boundary A md) md wd callback ≤ 160000 * S := by omega
  have hx : 1 ≤ 4 ^ wd := Nat.one_le_pow _ _ (by decide)
  have hy : 1 ≤ 4 ^ md := Nat.one_le_pow _ _ (by decide)
  have hscan : callback + 110 * wd + 36 ≤ 147 * S := by dsimp [S]; omega
  have hsw : 4 ^ wd * (callback + 110 * wd + 36) + 3 ≤ 150 * S * 4 ^ wd := by
    have hmul := Nat.mul_le_mul_left (4 ^ wd) hscan
    have hpos : 1 ≤ S * 4 ^ wd := by nlinarith
    nlinarith
  have hT := candidateBudget_le (boundary A md) md wd callback
    (4 ^ wd * (callback + 110 * wd + 36) + 3)
  have hST : S ≤ S * 4 ^ wd := by nlinarith
  have hT' : candidateBudget (boundary A md) md wd callback
      (4 ^ wd * (callback + 110 * wd + 36) + 3) ≤ 158000 * S * 4 ^ wd := by
    nlinarith
  have hmd : md ≤ S := by dsimp [S]; omega
  have hbody : candidateBudget (boundary A md) md wd callback
      (4 ^ wd * (callback + 110 * wd + 36) + 3) +
      7 * (boundary A md + candidateSpace (boundary A md) md wd callback) +
      10 + 42 * md + 12 ≤ 1300000 * S * 4 ^ wd := by nlinarith
  have hmain := Nat.mul_le_mul_left (4 ^ md) hbody
  have htail : 3 + 15 * md + 4 * boundary A md + 17 ≤ 63 * S := by omega
  have hprod : S ≤ S * (4 ^ md * 4 ^ wd) := by
    have hp : 1 ≤ 4 ^ md * 4 ^ wd := by nlinarith
    nlinarith
  dsimp [timeBudget]
  change _ ≤ 4000000 * S * (4 ^ md * 4 ^ wd)
  nlinarith

/-- The retained code-search workspace contains no enumeration-domain factor. -/
theorem streamedCodeSpace_le (A md wd callback : ℕ) :
    spaceBudget md (boundary A md)
      (candidateSpace (boundary A md) md wd callback) ≤
      10000000 * (A + md + wd + callback + 1) := by
  let S := A + md + wd + callback + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hB : boundary A md ≤ 7 * S := by dsimp [boundary, S]; omega
  have hsum : boundary A md + md + wd + callback + 1 ≤ 8 * S := by
    dsimp [boundary, S]
    omega
  have hC := candidateSpace_le (boundary A md) md wd callback
  have hmd : md ≤ S := by dsimp [S]; omega
  have hm : max (56 * (boundary A md + candidateSpace (boundary A md) md wd callback) + 10)
      (48 * boundary A md + 7 * (6 * md + 1) + 4) ≤ 9000000 * S := by
    apply max_le <;> omega
  dsimp [spaceBudget]
  change _ ≤ 10000000 * S
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets
open SparseCodeSearch CodeChecks

/-- Actual local-search storage is quadratic in ordinary dimensions and words. -/
theorem localCodeSpace_polynomial (A t D d : ℕ) :
    localSpace A t D d ≤ 100000000000000 * (A + t + D + d + 1) ^ 2 := by
  have h := streamedCodeSpace_le A (t * D) D (OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackBudget t D d)
  let S := A + t + D + d + 1
  have ht : t ≤ S := by dsimp [S]; omega
  have hD : D ≤ S := by dsimp [S]; omega
  have hd : d ≤ S := by dsimp [S]; omega
  have hA : A ≤ S := by dsimp [S]; omega
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hp : S ≤ S ^ 2 := by nlinarith
  have hm : t * D ≤ S ^ 2 := by nlinarith [Nat.mul_le_mul ht hD]
  change _ ≤ 100000000000000 * S ^ 2
  simpa only [localSpace] using (show spaceBudget (t * D) (boundary A (t * D))
    (candidateSpace (boundary A (t * D)) (t * D) D
      (OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackBudget t D d)) ≤
      100000000000000 * S ^ 2 by
        calc
          _ ≤ _ := h
          _ ≤ _ := by rw [local_budget]; nlinarith)

/-- Graph-word comparisons contribute only a fixed quadratic storage bound. -/
theorem graphCodeSpace_polynomial (A D r ql Dl : ℕ) :
    graphSpace A D r ql Dl ≤ 100000000000000 * (A + D + r + ql + Dl + 1) ^ 2 := by
  have h := streamedCodeSpace_le A (D * r) r
    (OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget D r ql Dl)
  let S := A + D + r + ql + Dl + 1
  have hD : D ≤ S := by dsimp [S]; omega
  have hr : r ≤ S := by dsimp [S]; omega
  have hq : ql ≤ S := by dsimp [S]; omega
  have hd : Dl ≤ S := by dsimp [S]; omega
  have hA : A ≤ S := by dsimp [S]; omega
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hp : S ≤ S ^ 2 := by nlinarith
  have hm : D * r ≤ S ^ 2 := by nlinarith [Nat.mul_le_mul hD hr]
  have hs : 2 * (ql + Dl + D) + 4 ≤ 6 * S := by dsimp [S]; omega
  have hsq : (2 * (ql + Dl + D) + 4) ^ 2 ≤ 36 * S ^ 2 := by nlinarith
  change _ ≤ 100000000000000 * S ^ 2
  simpa only [graphSpace] using (show spaceBudget (D * r) (boundary A (D * r))
    (candidateSpace (boundary A (D * r)) (D * r) r
      (OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget D r ql Dl)) ≤
      100000000000000 * S ^ 2 by
        calc
          _ ≤ _ := h
          _ ≤ _ := by rw [graph_budget]; nlinarith)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets
open SparseCodeSearch CodeChecks
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCost

private theorem localNumeric_lower (a w t D d U P Q : ℕ) (hP : 1 ≤ P) (hQ : 1 ≤ Q) :
    U + D + localCallback U t D d + 1 ≤ 2 * localNumeric a w t D d U P Q ∧
    Q * P ≤ localNumeric a w t D d U P Q := by
  let c := localCallback U t D d
  have hc : U + D + 1 ≤ c := by dsimp [c, localCallback, localWord, matrix2]; omega
  have hi : P * (c + 1) ≤ localCandidate U t D d P := by
    dsimp [localCandidate, localVerifier, c]
    nlinarith
  have ho : Q * localCandidate U t D d P ≤ localNumeric a w t D d U P Q := by
    unfold localNumeric
    nlinarith
  have hb : Q * P * (c + 1) ≤ localNumeric a w t D d U P Q := by
    have hm := Nat.mul_le_mul_left Q hi
    nlinarith
  have hpq : 1 ≤ Q * P := by nlinarith
  have hcs : c + 1 ≤ Q * P * (c + 1) := by nlinarith
  have hd : Q * P ≤ Q * P * (c + 1) := by nlinarith
  constructor
  · change U + D + c + 1 ≤ _
    omega
  · omega

private theorem graphNumeric_lower (a w D r ql Dl U P Q : ℕ)
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) :
    U + r + graphCallback U D r ql Dl + 1 ≤ 2 * graphNumeric a w D r ql Dl U P Q ∧
    Q * P ≤ graphNumeric a w D r ql Dl U P Q := by
  let c := graphCallback U D r ql Dl
  have hc : U + r + 1 ≤ c := by dsimp [c, graphCallback, graphWord, matrix2]; omega
  have hi : P * (c + 1) ≤ graphCandidate U D r ql Dl P := by
    dsimp [graphCandidate, graphVerifier, c]
    nlinarith
  have ho : Q * graphCandidate U D r ql Dl P ≤ graphNumeric a w D r ql Dl U P Q := by
    unfold graphNumeric
    nlinarith
  have hb : Q * P * (c + 1) ≤ graphNumeric a w D r ql Dl U P Q := by
    have hm := Nat.mul_le_mul_left Q hi
    nlinarith
  have hpq : 1 ≤ Q * P := by nlinarith
  have hcs : c + 1 ≤ Q * P * (c + 1) := by nlinarith
  have hd : Q * P ≤ Q * P * (c + 1) := by nlinarith
  constructor
  · change U + r + c + 1 ≤ _
    omega
  · omega

private theorem localCallback_eq (t D d : ℕ) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackBudget t D d = localCallback (t * D) t D d := by
  rw [local_budget]
  unfold localCallback localWord matrix2
  ring

private theorem graphCallback_eq (D r ql Dl : ℕ) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget D r ql Dl =
      graphCallback (D * r) D r ql Dl := by
  rw [graph_budget]
  unfold graphCallback graphWord matrix2
  ring

/-- The entire new local search is dominated by a fixed cubic power of the
original explicit worst-case budget, not by the old successful execution time. -/
theorem localCodeTime_le_numeric (A a w t D d : ℕ) :
    localTime A t D d ≤
      8000000 * (A + localNumeric a w t D d (t * D) (3 ^ D) (3 ^ (t * D)) + 1) ^ 3 := by
  let N := localNumeric a w t D d (t * D) (3 ^ D) (3 ^ (t * D))
  have hl := localNumeric_lower a w t D d (t * D) (3 ^ D) (3 ^ (t * D))
    (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow _ _ (by decide))
  have hs : A + t * D + D + OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackBudget t D d + 1 ≤
      2 * (A + N + 1) := by rw [localCallback_eq]; dsimp [N]; omega
  have hd : 4 ^ (t * D) * 4 ^ D ≤ N ^ 2 :=
    (local_attempts_le_square t D).trans (Nat.pow_le_pow_left hl.2 2)
  calc
    _ ≤ 4000000 * (A + t * D + D + OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackBudget t D d + 1) *
        (4 ^ (t * D) * 4 ^ D) := streamedCodeTime_le A (t * D) D _
    _ ≤ 4000000 * (2 * (A + N + 1)) * (A + N + 1) ^ 2 := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 4000000 hs)
        (hd.trans (Nat.pow_le_pow_left (by omega) 2))
    _ = _ := by dsimp [N]; ring

/-- Both graph tuple domains are charged, including all rejected candidates. -/
theorem graphCodeTime_le_numeric (A a w D r ql Dl : ℕ) :
    graphTime A D r ql Dl ≤
      8000000 * (A + graphNumeric a w D r ql Dl (D * r) (2 ^ r) (2 ^ (D * r)) + 1) ^ 3 := by
  let N := graphNumeric a w D r ql Dl (D * r) (2 ^ r) (2 ^ (D * r))
  have hl := graphNumeric_lower a w D r ql Dl (D * r) (2 ^ r) (2 ^ (D * r))
    (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow _ _ (by decide))
  have hs : A + D * r + r + OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget D r ql Dl + 1 ≤
      2 * (A + N + 1) := by rw [graphCallback_eq]; dsimp [N]; omega
  have hd : 4 ^ (D * r) * 4 ^ r ≤ N ^ 2 := by
    rw [graph_attempts_eq_square]
    exact Nat.pow_le_pow_left hl.2 2
  calc
    _ ≤ 4000000 * (A + D * r + r + OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget D r ql Dl + 1) *
        (4 ^ (D * r) * 4 ^ r) := streamedCodeTime_le A (D * r) r _
    _ ≤ 4000000 * (2 * (A + N + 1)) * (A + N + 1) ^ 2 := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 4000000 hs)
        (hd.trans (Nat.pow_le_pow_left (by omega) 2))
    _ = _ := by dsimp [N]; ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets
open SparseCodeSearch CodeChecks
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCost
open OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement
open Filter
open scoped Topology

/-- One fixed envelope covers both complete native code searches and their
retained outputs. No accepting candidate is a hypothesis. -/
theorem codeTime_le_envelope (A t D d r ql Dl H W : ℕ)
    (ht : t ≤ H) (hD : D ≤ H) (hd : d ≤ H) (hr : r ≤ H)
    (hq : ql ≤ W) (hDl : Dl ≤ W) :
    localTime A t D d + graphTime A D r ql Dl + 1 ≤
      16000001 * (A + envelope 3000000000000 H W + 1) ^ 3 := by
  have he := combinedNumeric_bound 0 0 0 0 t D d r ql Dl 1 1 H W
    3000000000000 ht hD hd hr hq hDl (by norm_num)
  simp only [one_mul] at he
  have hl := localCodeTime_le_numeric A 0 0 t D d
  have hg := graphCodeTime_le_numeric A 0 0 D r ql Dl
  have hle : A + localNumeric 0 0 t D d (t * D) (3 ^ D) (3 ^ (t * D)) + 1 ≤
      A + envelope 3000000000000 H W + 1 := by omega
  have hge : A + graphNumeric 0 0 D r ql Dl (D * r) (2 ^ r) (2 ^ (D * r)) + 1 ≤
      A + envelope 3000000000000 H W + 1 := by omega
  have hl' := hl.trans (Nat.mul_le_mul_left 8000000 (Nat.pow_le_pow_left hle 3))
  have hg' := hg.trans (Nat.mul_le_mul_left 8000000 (Nat.pow_le_pow_left hge 3))
  have hp : 1 ≤ (A + envelope 3000000000000 H W + 1) ^ 3 :=
    Nat.one_le_pow _ _ (by omega)
  omega

/-- Fixed cubic numerical overhead preserves the supplied exponent scale. -/
theorem cubic_cost_runtimeBound (cost A E n C : ℕ)
    (hc : cost ≤ C * (A + E + 1) ^ 3)
    (he : (E : ℝ) ≤ (2 : ℝ) ^ runtimeScale n) :
    (cost : ℝ) ≤ runtimeBound (8 * (C : ℝ)) 3 3 A n := by
  let R : ℝ := (2 : ℝ) ^ runtimeScale n
  have hr1 : 1 ≤ R := Real.one_le_rpow (by norm_num) (runtimeScale_nonneg n)
  have hsum : (A : ℝ) + E + 1 ≤ 2 * ((A : ℝ) + 1) * R := by
    have hA : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
    change (E : ℝ) ≤ R at he
    nlinarith
  have hc' : (cost : ℝ) ≤ (C : ℝ) * ((A : ℝ) + E + 1) ^ 3 := by exact_mod_cast hc
  calc
    _ ≤ (C : ℝ) * ((A : ℝ) + E + 1) ^ 3 := hc'
    _ ≤ (C : ℝ) * (2 * ((A : ℝ) + 1) * R) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (add_nonneg (add_nonneg (Nat.cast_nonneg A) (Nat.cast_nonneg E)) zero_le_one) hsum 3)
        (Nat.cast_nonneg C)
    _ = runtimeBound (8 * (C : ℝ)) 3 3 A n := by
      unfold runtimeBound R
      rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast (by norm_num)]
      norm_num
      rw [mul_comm (runtimeScale n) 3]
      ring

/-- The input-independent cubic comparison preserves the original runtime
scale. Arbitrarily large physical input words remain in an explicit polynomial. -/
theorem eventually_codeTime (heightCoefficient heightDegree wordDegree : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ A t D d r ql Dl H : ℕ,
      t ≤ H → D ≤ H → d ≤ H → r ≤ H →
      H ≤ heightCoefficient * OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.L n ^ heightDegree →
      ql ≤ (n + 1) ^ wordDegree → Dl ≤ (n + 1) ^ wordDegree →
      ((localTime A t D d + graphTime A D r ql Dl + 1 : ℕ) : ℝ) ≤
        runtimeBound 128000008 3 3 A n := by
  filter_upwards [eventually_envelope 3000000000000 heightCoefficient heightDegree wordDegree]
    with n hn A t D d r ql Dl H ht hD hd hr hH hq hDl
  have h := cubic_cost_runtimeBound
    (localTime A t D d + graphTime A D r ql Dl + 1) A
    (envelope 3000000000000 H (max ql Dl)) n 16000001
    (codeTime_le_envelope A t D d r ql Dl H (max ql Dl)
      ht hD hd hr (le_max_left _ _) (le_max_right _ _))
    (hn H (max ql Dl) hH (max_le hq hDl))
  norm_num only [Nat.cast_ofNat] at h
  exact h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchBudgets
