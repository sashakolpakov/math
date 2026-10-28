import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintEntryProgram

namespace OAI.Algorithms

/-! Polynomial caps for the concrete joint, extended-joint and defect-entry
program budgets. Every changing parameter is bounded by the local size U. -/

namespace SubexponentialSAT.Subexp.MatrixEntryBudgetBounds

open MulticolorTypes MatrixWordEncoding
open MatrixEntryProgram

variable {r Q Δ : ℕ}

theorem prepareCost_typed (p : ℕ) [Fact p.Prime] (i : Fin Δ)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) (A B : ℕ) :
    prepareCost (typedInput p i u y xs (fun _ => false)) A B =
      13 * A + 6 * B + 7 * Q + 14 * width p +
        14 * xs.length * (width p + 1) + 52 := by
  simp +decide [prepareCost, typedInput, input, CoefficientPascalProgram.valueWords_length]
  ring

theorem cleanupCost_finished (p : ℕ) [Fact p.Prime] (i : Fin Δ)
    (u y : UniversalType r Q Δ) (xs ys : List (ZMod p)) (A B : ℕ) :
    cleanupCost (finished (typedInput p i u y xs (fun _ => false))
      (fun _ => false) p ys A B) =
      8 * width p + ys.length * (4 * width p + 4) + 2 * A + 2 * B + 9 * Q + 51 := by
  change (([[], [], modulus p, frameWidthWord p,
    CoefficientPascalProgram.valueWords p ys, [], word p 0, [], [],
    List.replicate ys.length true, [], List.replicate A true,
    List.replicate B true] : List (List Bool)).map (fun bits => 2 * bits.length + 3)).sum +
      (7 * (List.replicate Q true).length + 5) +
      (2 * (List.replicate Q true).length + 3) = _
  simp [frameWidthWord, CoefficientPascalProgram.valueWords_length]
  ring

theorem cleanupCost_zero (p : ℕ) [Fact p.Prime] (i : Fin Δ)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) (A B : ℕ) :
    cleanupCost (zeroResult (typedInput p i u y xs (fun _ => false))
      (fun _ => false) A B) = 2 * A + 2 * B + 9 * Q + 47 := by
  simp +decide [cleanupCost, cleanupPorts, zeroResult, counted, copied,
    StackRoutines.copyStacks, typedInput, input]
  ring

theorem typeWidth_le {U : ℕ} (hr : r ≤ U) (hQ : Q ≤ U) (hΔ : Δ ≤ U) :
    CollisionProgram.typeWidth r Q Δ ≤ (U + 1) ^ 3 := by
  unfold CollisionProgram.typeWidth
  calc
    _ ≤ ((U + 1) * (U + 1)) * (U + 1) := by gcongr <;> omega
    _ = _ := by ring

theorem scanStageCost_le {U : ℕ} (i : Fin Δ)
    (hr : r ≤ U) (hQ : Q ≤ U) (hΔ : Δ ≤ U) :
    scanStageCost r Q Δ i.val ≤ 1200 * (U + 1) ^ 3 := by
  let s := U + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s ^ 2 := by nlinarith
  have hs3 : s ^ 2 ≤ s ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hi : i.val + 1 ≤ s := by have := i.isLt; dsimp [s]; omega
  have hQr : Q * r ≤ s ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (show Q ≤ s by dsimp [s]; omega)
      (show r ≤ s by dsimp [s]; omega)
  have htype := typeWidth_le hr hQ hΔ
  change CollisionProgram.typeWidth r Q Δ ≤ s ^ 3 at htype
  change _ ≤ 1200 * s ^ 3
  calc
    _ ≤ (7 * s + 5) + (36 * s ^ 3 + 4 * s * (14 * s ^ 2 + 17) +
        203 * s ^ 2 + 265) + (s * (208 * s + 149) + 3) := by
      unfold scanStageCost
      gcongr <;> dsimp [s] at * <;> omega
    _ ≤ _ := by nlinarith only [hs, hs2, hs3]

theorem guardStageCost_le {U : ℕ} (i : Fin Δ) (t : Fin Q)
    (hr : r ≤ U) (hQ : Q ≤ U) (hΔ : Δ ≤ U) :
    MatrixExtendedEntryProgram.guardStageCost r Q Δ i.val t.val ≤ 2000 * (U + 1) ^ 3 := by
  let s := U + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s ^ 2 := by nlinarith
  have hs3 : s ^ 2 ≤ s ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hi : i.val + 1 ≤ s := by have := i.isLt; dsimp [s]; omega
  have ht : t.val ≤ s := by have := t.isLt; dsimp [s]; omega
  have hQr : Q * r ≤ s ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (show Q ≤ s by dsimp [s]; omega)
      (show r ≤ s by dsimp [s]; omega)
  have htype := typeWidth_le hr hQ hΔ
  change CollisionProgram.typeWidth r Q Δ ≤ s ^ 3 at htype
  change _ ≤ 2000 * s ^ 3
  calc
    _ ≤ (36 * s ^ 3 + 4 * s * (14 * s ^ 2 + 17) + 203 * s ^ 2 + 265) +
        (4 * (9 * s ^ 2 + s * (14 * s + 17) + 30 * s + 43) + 1) +
        (81 * s + 107) + (8 * s ^ 2 + 8 * s + 24) := by
      unfold MatrixExtendedEntryProgram.guardStageCost
      gcongr <;> dsimp [s] at * <;> omega
    _ ≤ _ := by nlinarith only [hs, hs2, hs3]

theorem coefficientStageCost_le (p R Q B U : ℕ)
    (hR : R ≤ U) (hQ : Q ≤ U) (hB : B ≤ U) (hw : width p ≤ U) :
    coefficientStageCost p R Q B ≤ 200000 * (U + 1) ^ 4 := by
  let s := U + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s ^ 2 := by nlinarith
  have hs3 : s ^ 2 ≤ s ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hs4 : s ^ 3 ≤ s ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  change _ ≤ 200000 * s ^ 4
  calc
    _ ≤ MatrixPaddingProgram.cost (s * (2 * s + 1)) s (s + 1) + 1 +
        (7 * s + 5) + (s * (MatrixPascalProgram.passBudget (s + (s + 1)) s + 2) + 3) := by
      unfold coefficientStageCost MatrixPaddingProgram.cost MatrixPascalProgram.passBudget
        CoefficientPascalProgram.budget CoefficientPascalProgram.setupBudget
        CoefficientPascalProgram.rowBudget
      gcongr <;> dsimp [s] <;> omega
    _ ≤ _ := by
      unfold MatrixPaddingProgram.cost MatrixPascalProgram.passBudget
        CoefficientPascalProgram.budget CoefficientPascalProgram.setupBudget
        CoefficientPascalProgram.rowBudget
      nlinarith only [hs, hs2, hs3, hs4]

theorem finishEntryCost_le (p A U : ℕ) (hA : A ≤ U) (hw : width p ≤ U) :
    finishEntryCost p A ≤ 25000 * (U + 1) ^ 2 := by
  let s := U + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s ^ 2 := by nlinarith
  change _ ≤ 25000 * s ^ 2
  calc
    _ ≤ 2 * (7 * s + 5) + 2 + (7 * s + 5) +
        (MatrixWordSelectProgram.budget s s + 1) + (6073 * (s + 1)^2 + 3 * s + 7) := by
      unfold finishEntryCost MatrixWordSelectProgram.budget
      gcongr <;> dsimp [s] <;> omega
    _ ≤ _ := by unfold MatrixWordSelectProgram.budget; nlinarith only [hs, hs2]

theorem entry_programBudget_le (p : ℕ) [Fact p.Prime] (i : Fin Δ)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) (U : ℕ)
    (hr : r ≤ U) (hQ : Q ≤ U) (hΔ : Δ ≤ U) (hR : xs.length ≤ U) (hw : width p ≤ U) :
    MatrixEntryProgram.programBudget p i u y xs ≤ 300000 * (U + 1) ^ 4 := by
  let s := U + 1
  let A := MatrixScanProgram.unchangedCount (MatrixEntryEvaluation.rows i u y)
  let B := MatrixScanProgram.transposedCount (MatrixEntryEvaluation.rows i u y)
  let ys := MatrixPascalProgram.repeated p B (paddedCoefficients xs Q)
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s ^ 2 := by nlinarith
  have hs3 : s ^ 2 ≤ s ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hs4 : s ^ 3 ≤ s ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hA : A ≤ U := (MatrixEntryEvaluation.unchangedCount_le i u y).trans hQ
  have hB : B ≤ U := (MatrixEntryEvaluation.transposedCount_le i u y).trans hQ
  have hAm : A - 1 ≤ U := (Nat.sub_le _ _).trans hA
  have hy : ys.length ≤ 3 * s := by
    simp only [ys, MatrixPascalProgram.repeated_length, paddedCoefficients,
      List.length_append, List.length_replicate]
    dsimp [s]; omega
  have hprepare : prepareCost (typedInput p i u y xs (fun _ => false)) (A - 1) B ≤ 128 * s ^ 2 := by
    rw [prepareCost_typed]
    calc
      _ ≤ 13 * s + 6 * s + 7 * s + 14 * s + 14 * s * (s + 1) + 52 := by
        gcongr <;> dsimp [s] <;> omega
      _ ≤ _ := by nlinarith only [hs, hs2]
  have hclean : cleanupCost (finished (typedInput p i u y xs (fun _ => false))
      (fun _ => false) p ys (A - 1) B) ≤ 128 * s ^ 2 := by
    rw [cleanupCost_finished]
    calc
      _ ≤ 8 * s + (3 * s) * (4 * s + 4) + 2 * s + 2 * s + 9 * s + 51 := by
        gcongr <;> dsimp [s] at * <;> omega
      _ ≤ _ := by nlinarith only [hs, hs2]
  have hzero : cleanupCost (zeroResult (typedInput p i u y xs (fun _ => false))
      (fun _ => false) A B) ≤ 60 * s := by
    rw [cleanupCost_zero]
    dsimp [s] at *
    omega
  have hscan := scanStageCost_le i hr hQ hΔ
  have hcoefficient := coefficientStageCost_le p xs.length Q B U hR hQ hB hw
  have hfinish := finishEntryCost_le p (A - 1) U hAm hw
  change scanStageCost r Q Δ i.val ≤ 1200 * s ^ 3 at hscan
  change coefficientStageCost p xs.length Q B ≤ 200000 * s ^ 4 at hcoefficient
  change finishEntryCost p (A - 1) ≤ 25000 * s ^ 2 at hfinish
  have hword : (word p (0 : ZMod p)).length ≤ s := (word_length p 0).le.trans (by dsimp [s]; omega)
  change _ ≤ 300000 * s ^ 4
  unfold MatrixEntryProgram.programBudget positiveCost
  change scanStageCost r Q Δ i.val +
    (prepareCost (typedInput p i u y xs (fun _ => false)) (A - 1) B +
      coefficientStageCost p xs.length Q B + finishEntryCost p (A - 1)) +
    cleanupCost (finished (typedInput p i u y xs (fun _ => false)) (fun _ => false) p ys (A - 1) B) +
    (7 * (word p (0 : ZMod p)).length + 5) +
    cleanupCost (zeroResult (typedInput p i u y xs (fun _ => false)) (fun _ => false) A B) + 2 ≤ _
  nlinarith only [hprepare, hclean, hzero, hscan, hcoefficient, hfinish,
    hword, hs, hs2, hs3, hs4]

theorem extended_programBudget_le (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) (U : ℕ)
    (hr : r ≤ U) (hQ : Q ≤ U) (hΔ : Δ ≤ U) (hR : xs.length ≤ U) (hw : width p ≤ U) :
    MatrixExtendedEntryProgram.programBudget p i t u y xs ≤ 400000 * (U + 1) ^ 4 := by
  have he := entry_programBudget_le p i u y xs U hr hQ hΔ hR hw
  have hg := guardStageCost_le i t hr hQ hΔ
  have hs : 1 ≤ U + 1 := by omega
  have h13 : U + 1 ≤ (U + 1) ^ 3 := by
    simpa using Nat.pow_le_pow_right hs (show 1 ≤ 3 by decide)
  have h34 : (U + 1) ^ 3 ≤ (U + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold MatrixExtendedEntryProgram.programBudget
  nlinarith only [he, hg, hw, hs, h13, h34]

theorem constraint_programBudget_le (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) (U : ℕ)
    (hr : r ≤ U) (hQ : Q ≤ U) (hΔ : Δ ≤ U) (hR : xs.length ≤ U) (hw : width p ≤ U) :
    ConstraintEntryProgram.programBudget p i t u y xs ≤ 500000 * (U + 1) ^ 4 := by
  have he := extended_programBudget_le p i t u y xs U hr hQ hΔ hR hw
  have ht := typeWidth_le hr hQ hΔ
  have hw2 := Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 2
  have hs : 1 ≤ U + 1 := by omega
  have h12 : U + 1 ≤ (U + 1) ^ 2 := by nlinarith
  have h23 : (U + 1) ^ 2 ≤ (U + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h34 : (U + 1) ^ 3 ≤ (U + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold ConstraintEntryProgram.programBudget
  nlinarith only [he, ht, hw2, hs, h12, h23, h34]

theorem constraint_programBudget_le_sixth (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) (U : ℕ)
    (hr : r ≤ U) (hQ : Q ≤ U) (hΔ : Δ ≤ U) (hR : xs.length ≤ U) (hw : width p ≤ U) :
    ConstraintEntryProgram.programBudget p i t u y xs ≤ 1000000 * (U + 1) ^ 6 := by
  apply (constraint_programBudget_le p i t u y xs U hr hQ hΔ hR hw).trans
  exact Nat.mul_le_mul (by decide)
    (Nat.pow_le_pow_right (by omega : 0 < U + 1) (by omega))

end SubexponentialSAT.Subexp.MatrixEntryBudgetBounds

end OAI.Algorithms
