import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpVertexPairComplexity
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialStep
import OAI.Algorithms.SubexponentialSAT.ScoreBuilderSizeBounds

namespace OAI.Algorithms

/-! Arithmetic envelopes used by the complete assignment frontend. The size
parameter includes every growing numerical parameter and the actual input
scope-byte count. No generated-tape size or body runtime is supplied. -/

namespace SubexponentialSAT.Subexp.AssignmentFrontendBounds

open BitProgram StructuredCalls MulticolorTypes

def sourceSize (r Q Δ D : ℕ) (scopes : List (List ℕ)) : ℕ :=
  D + scopes.length + blockSize r Q Δ + Q + r + Δ +
    (SubexpPlanAlphabetBase.scopeBytes scopes).length + 1

def scoreCoefficient : ℕ := 10000 * 31 ^ 6 * 1025 ^ 12
def inputCoefficient : ℕ := 2000101

def coefficient : ℕ :=
  2000000 + 20000 * inputCoefficient ^ 4 + 40 * inputCoefficient ^ 2 +
    2 * (scoreCoefficient + 40003) + 6

theorem le_power {S k : ℕ} (hS : 1 ≤ S) (hk : 1 ≤ k) : S ≤ S ^ k := by
  simpa only [pow_one] using Nat.pow_le_pow_right hS hk

theorem sourceSize_pos (r Q Δ D : ℕ) (scopes : List (List ℕ)) :
    1 ≤ sourceSize r Q Δ D scopes := by
  unfold sourceSize
  omega

theorem seedCount_le (r Q Δ D : ℕ) (scopes : List (List ℕ)) :
    scopes.length + (Δ + 1) * D ≤ 2 * sourceSize r Q Δ D scopes ^ 2 := by
  let S := sourceSize r Q Δ D scopes
  have hS := sourceSize_pos r Q Δ D scopes
  have hE : scopes.length ≤ S := by dsimp [S, sourceSize]; omega
  have hD : D ≤ S := by dsimp [S, sourceSize]; omega
  have hd : Δ + 1 ≤ S := by dsimp [S, sourceSize]; omega
  have hprod : (Δ + 1) * D ≤ S ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hd hD
  have hS2 : S ≤ S ^ 2 := le_power hS (by decide)
  change scopes.length + (Δ + 1) * D ≤ 2 * S ^ 2
  omega

theorem pair_polynomial_le (r Q Δ D : ℕ) (scopes : List (List ℕ)) :
    60 * (SubexpVertexPairProgram.polynomialBound D Δ scopes +
      (SubexpPlanAlphabetBase.scopeBytes scopes).length + 4) ≤
      2000000 * sourceSize r Q Δ D scopes ^ 5 := by
  let S := sourceSize r Q Δ D scopes
  have hS : 1 ≤ S := sourceSize_pos r Q Δ D scopes
  have hD : D ≤ S := by dsimp [S, sourceSize]; omega
  have hE : scopes.length ≤ S := by dsimp [S, sourceSize]; omega
  have hd : Δ + 1 ≤ S := by dsimp [S, sourceSize]; omega
  have hd' : Δ ≤ S := by omega
  have hB : (SubexpPlanAlphabetBase.scopeBytes scopes).length ≤ S := by
    dsimp [S, sourceSize]; omega
  have hS2 : S ≤ S ^ 2 := le_power hS (by decide)
  have hS3 : S ≤ S ^ 3 := le_power hS (by decide)
  have hS4 : S ≤ S ^ 4 := le_power hS (by decide)
  have hS5 : S ≤ S ^ 5 := le_power hS (by decide)
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have h24 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
  have h25 : S ^ 2 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h45 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h13 : 1 ≤ S ^ 3 := hS.trans hS3
  have h14 : 1 ≤ S ^ 4 := hS.trans hS4
  have h15 : 1 ≤ S ^ 5 := hS.trans hS5
  have hM : scopes.length + (Δ + 1) * D ≤ 2 * S ^ 2 := seedCount_le r Q Δ D scopes
  have hp : SubexpPlanAlphabetBase.planWordBound D Δ scopes ≤ 7 * S ^ 3 := by
    calc
      _ ≤ 1 + (2 * (2 * S ^ 2) + 2) * S := by
        unfold SubexpPlanAlphabetBase.planWordBound
        gcongr
      _ ≤ 7 * S ^ 3 := by ring_nf; omega
  have hi : SubexpIncidencePlanProgram.inputSize D Δ D scopes ≤ 2 * S := by
    change (SubexpPlanAlphabetBase.scopeBytes scopes).length + D + Δ + D + 1 ≤ 2 * S
    dsimp [S, sourceSize]
    omega
  have hcopy : (SubexpPlanAlphabetBase.scopeBytes scopes).length + D + Δ + D ≤ 2 * S := by
    change (SubexpPlanAlphabetBase.scopeBytes scopes).length + D + Δ + D + 1 ≤ 2 * S at hi
    omega
  have hprod : D * Δ ≤ S ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hD hd'
  have hclear : 2 * scopes.length + 2 * D + D * Δ + 3 * Δ + 3 * D + 1 ≤ 12 * S ^ 2 := by
    omega
  have hu : SubexpPlanAlphabetBase.uniformCallbackBound D Δ scopes ≤ 10000 * S ^ 3 := by
    calc
      _ ≤ 1000 * (2 * S) ^ 3 + 7 * (2 * S) + 34 * (7 * S ^ 3) +
          2 * (12 * S ^ 2) + 106 := by
        unfold SubexpPlanAlphabetBase.uniformCallbackBound
        gcongr
      _ ≤ 10000 * S ^ 3 := by ring_nf; omega
  have ha : SubexpPlanAlphabetBase.polynomialBound D Δ scopes ≤ 10100 * S ^ 4 := by
    calc
      _ ≤ 6 * S ^ 2 + 17 * S + 15 + S * (6 * S + 10000 * S ^ 3 + 7) := by
        unfold SubexpPlanAlphabetBase.polynomialBound
        gcongr
      _ ≤ 10100 * S ^ 4 := by ring_nf; omega
  have hv : SubexpVertexPairProgram.polynomialBound D Δ scopes ≤ 20000 * S ^ 5 := by
    calc
      _ ≤ 10100 * S ^ 4 + (S * (2 * (7 * S ^ 3) + 1)) * (61 * S + 45) +
          48 * S ^ 2 + 73 * S + 78 := by
        unfold SubexpVertexPairProgram.polynomialBound
        gcongr
      _ ≤ 20000 * S ^ 5 := by ring_nf; omega
  calc
    _ ≤ 60 * (20000 * S ^ 5 + S + 4) := by
      gcongr
    _ ≤ 2000000 * S ^ 5 := by omega

theorem selection_numeric_le (S q weight total width : ℕ) (hS : 1 ≤ S)
    (hq : q ≤ S) (hweight : weight ≤ S ^ 4) (ht : total ≤ 2 * S ^ 2)
    (hw : width ≤ S ^ 2) :
    SequentialProgram.selectionBudget q weight total width ≤ 40000 * S ^ 10 := by
  have h1 : S ≤ S ^ 10 := le_power hS (by decide)
  have h2 : S ^ 2 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  have h3 : S ^ 3 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  have h4 : S ^ 4 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  have h5 : S ^ 5 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  have h6 : S ^ 6 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  calc
    _ ≤ SequentialProgram.selectionBudget S (S ^ 4) (2 * S ^ 2) (S ^ 2) := by
      unfold SequentialProgram.selectionBudget SequentialProgram.minimumBudget
        SequentialProgram.updateBudget SequentialProgram.recordBudget
      gcongr
    _ ≤ 40000 * S ^ 10 := by
      unfold SequentialProgram.selectionBudget SequentialProgram.minimumBudget
        SequentialProgram.updateBudget SequentialProgram.recordBudget
      ring_nf
      omega

theorem selection_budget_le (r Q Δ D : ℕ) (scopes : List (List ℕ)) (hr : 0 < r) :
    SequentialProgram.selectionBudget (r ^ Q) (D ^ 2 * (blockSize r Q Δ) ^ 2)
      (scopes.length + (Δ + 1) * D) (Q * r) ≤ 40000 * sourceSize r Q Δ D scopes ^ 10 := by
  let S := sourceSize r Q Δ D scopes
  have hS : 1 ≤ S := sourceSize_pos r Q Δ D scopes
  have hD : D ≤ S := by dsimp [S, sourceSize]; omega
  have hN : blockSize r Q Δ ≤ S := by dsimp [S, sourceSize]; omega
  have hQ : Q ≤ S := by dsimp [S, sourceSize]; omega
  have hrS : r ≤ S := by dsimp [S, sourceSize]; omega
  apply selection_numeric_le S _ _ _ _ hS
  · exact (ScoreBuilderSizeBounds.wordChoices_le r Q Δ (blockSize r Q Δ) (by omega) rfl).trans hN
  · calc
      _ ≤ S ^ 2 * S ^ 2 := Nat.mul_le_mul (Nat.pow_le_pow_left hD 2) (Nat.pow_le_pow_left hN 2)
      _ = _ := by ring
  · exact seedCount_le r Q Δ D scopes
  · simpa only [pow_two] using Nat.mul_le_mul hQ hrS

theorem input_expression_le (r Q Δ D : ℕ) (scopes : List (List ℕ))
    (pairBits : ℕ) (hr : 0 < r)
    (hp : pairBits ≤ 2000000 * sourceSize r Q Δ D scopes ^ 5) :
    let M := scopes.length + (Δ + 1) * D
    1 + r + Q + Δ + D + scopes.length + (Δ + 1) + 2 * (Δ + 1) + Q * r +
      M + r ^ Q + (1 + (2 * r + 2) * r) + (1 + (2 * (Q * r) + 2) * r ^ Q) + Q * r +
      r ^ Q * (Q * r) + (1 + (2 * M + 2) * M) + pairBits ≤
        2000100 * sourceSize r Q Δ D scopes ^ 5 := by
  let S := sourceSize r Q Δ D scopes
  let M := scopes.length + (Δ + 1) * D
  change pairBits ≤ 2000000 * S ^ 5 at hp
  have hS : 1 ≤ S := sourceSize_pos r Q Δ D scopes
  have hD : D ≤ S := by dsimp [S, sourceSize]; omega
  have hE : scopes.length ≤ S := by dsimp [S, sourceSize]; omega
  have hQ : Q ≤ S := by dsimp [S, sourceSize]; omega
  have hrS : r ≤ S := by dsimp [S, sourceSize]; omega
  have hdS : Δ + 1 ≤ S := by dsimp [S, sourceSize]; omega
  have hq : r ^ Q ≤ S := (ScoreBuilderSizeBounds.wordChoices_le r Q Δ
    (blockSize r Q Δ) (by omega) rfl).trans (by dsimp [S, sourceSize]; omega)
  have hM : M ≤ 2 * S ^ 2 := seedCount_le r Q Δ D scopes
  have hw : Q * r ≤ S ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hQ hrS
  have hS2 : S ≤ S ^ 2 := le_power hS (by decide)
  have hS3 : S ≤ S ^ 3 := le_power hS (by decide)
  have hS4 : S ≤ S ^ 4 := le_power hS (by decide)
  have hS5 : S ≤ S ^ 5 := le_power hS (by decide)
  have h25 : S ^ 2 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h35 : S ^ 3 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h45 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have hc : 1 + (2 * r + 2) * r ≤ 5 * S ^ 2 := by
    calc
      _ ≤ 1 + (2 * S + 2) * S := by gcongr
      _ ≤ 5 * S ^ 2 := by ring_nf; omega
  have hwords : 1 + (2 * (Q * r) + 2) * r ^ Q ≤ 5 * S ^ 3 := by
    calc
      _ ≤ 1 + (2 * S ^ 2 + 2) * S := by gcongr
      _ ≤ 5 * S ^ 3 := by ring_nf; omega
  have hflat : r ^ Q * (Q * r) ≤ S ^ 3 := by
    calc
      _ ≤ S * S ^ 2 := Nat.mul_le_mul hq hw
      _ = S ^ 3 := by ring
  have hseeds : 1 + (2 * M + 2) * M ≤ 13 * S ^ 4 := by
    calc
      _ ≤ 1 + (2 * (2 * S ^ 2) + 2) * (2 * S ^ 2) := by gcongr
      _ ≤ 13 * S ^ 4 := by
        have h24 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
        ring_nf
        omega
  change 1 + r + Q + Δ + D + scopes.length + (Δ + 1) + 2 * (Δ + 1) + Q * r +
    M + r ^ Q + (1 + (2 * r + 2) * r) + (1 + (2 * (Q * r) + 2) * r ^ Q) + Q * r +
    r ^ Q * (Q * r) + (1 + (2 * M + 2) * M) + pairBits ≤ 2000100 * S ^ 5
  omega

theorem score_expression_le (r Q Δ D : ℕ) (scopes : List (List ℕ)) (hr : 0 < r) :
    10000 * 31 ^ 6 *
      (16 * ((scopes.length + (Δ + 1) * D) + D + r ^ Q + Q * r + Δ + 1) ^ 2 + 1) ^ 12 *
        (r ^ Q) ^ (2 * (Δ + 1)) ≤
      scoreCoefficient * sourceSize r Q Δ D scopes ^ 50 := by
  have h := ScoreBuilderSizeBounds.runtime_expression_le D scopes.length
    (blockSize r Q Δ) Q r Δ (by omega) rfl
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (by unfold ScoreBuilderSizeBounds.sourceSize sourceSize; omega) 50))

theorem total_expression_le (S pair input init score select count : ℕ) (hS : 1 ≤ S)
    (hp : pair ≤ 2000000 * S ^ 5)
    (hi : input ≤ (20000 * inputCoefficient ^ 4) * S ^ 20)
    (hn : init ≤ (40 * inputCoefficient ^ 2) * S ^ 10)
    (hs : score ≤ scoreCoefficient * S ^ 50)
    (hsel : select ≤ 40000 * S ^ 10)
    (hm : count ≤ 2 * S ^ 2) :
    pair + (input + 1) + (init + (count * (score + select + 3) + 3) + 1) + 1 ≤
      coefficient * S ^ 60 := by
  have h1 : 1 ≤ S ^ 60 := Nat.one_le_pow _ _ hS
  have h5 : S ^ 5 ≤ S ^ 60 := Nat.pow_le_pow_right hS (by decide)
  have h10 : S ^ 10 ≤ S ^ 60 := Nat.pow_le_pow_right hS (by decide)
  have h20 : S ^ 20 ≤ S ^ 60 := Nat.pow_le_pow_right hS (by decide)
  have h50 : S ^ 10 ≤ S ^ 50 := Nat.pow_le_pow_right hS (by decide)
  have h150 : 1 ≤ S ^ 50 := Nat.one_le_pow _ _ hS
  have h52 : S ^ 52 ≤ S ^ 60 := Nat.pow_le_pow_right hS (by decide)
  have hbody : score + select + 3 ≤ (scoreCoefficient + 40003) * S ^ 50 := by
    have ht := hsel.trans (Nat.mul_le_mul_left 40000 h50)
    rw [Nat.add_mul]
    omega
  have hloop : count * (score + select + 3) ≤
      (2 * (scoreCoefficient + 40003)) * S ^ 60 := by
    calc
      _ ≤ (2 * S ^ 2) * ((scoreCoefficient + 40003) * S ^ 50) := Nat.mul_le_mul hm hbody
      _ = (2 * (scoreCoefficient + 40003)) * S ^ 52 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h52
  have hp' := hp.trans (Nat.mul_le_mul_left 2000000 h5)
  have hi' := hi.trans (Nat.mul_le_mul_left (20000 * inputCoefficient ^ 4) h20)
  have hn' := hn.trans (Nat.mul_le_mul_left (40 * inputCoefficient ^ 2) h10)
  unfold coefficient
  simp only [Nat.add_mul]
  omega

end SubexponentialSAT.Subexp.AssignmentFrontendBounds

end OAI.Algorithms
