import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheRow

namespace OAI.Algorithms

/-! Polynomial bounds for the measured Lagrange-cache schedule. The row
bound uses the published normalization and inner-loop costs. The numerical
outer schedule is independent of the execution module, avoiding an import
cycle when that module consumes this bound. -/

namespace SubexponentialSAT.SubexpLagrangeCacheCost

open SubexpLagrangeCachePreparation

def rowMajorant (W : ℕ) : ℕ :=
  300 * (W + 1) * (W + 1) +
    SubexpLagrangeCacheInner.loopBound W W W 0 W +
    (8 * W + 3) + (2 * W + 3) +
    4000000 * (W + 1)^5 +
    100 * (W + 1) * (4 * W + 1) + (26000 * (W + 1)^2 + 8 * W) + 2

theorem row_budget_le_majorant (D B i W : ℕ) (exponent counter : List Bool)
    (hD : D ≤ W) (hB : B ≤ W) (hi : i ≤ W)
    (he : exponent.length ≤ W) (hc : counter.length ≤ W)
    (hpower : BinaryArithmetic.toNat exponent ≤ W)
    (hcount : CounterPrograms.value counter ≤ W) :
    SubexpLagrangeCacheRow.budget D B i exponent counter ≤ rowMajorant W := by
  have hn := SubexpLagrangeNormalize.runtimeBound_le D B W exponent counter
    hD hB he hc hpower hcount
  unfold SubexpLagrangeCacheRow.budget rowMajorant SubexpLagrangeCacheInner.loopBound
  gcongr

theorem rowMajorant_le (W : ℕ) : rowMajorant W ≤ 8000000 * (W + 1)^6 := by
  unfold rowMajorant SubexpLagrangeCacheInner.loopBound
  ring_nf
  omega

theorem row_budget_le (D B i W : ℕ) (exponent counter : List Bool)
    (hD : D ≤ W) (hB : B ≤ W) (hi : i ≤ W)
    (he : exponent.length ≤ W) (hc : counter.length ≤ W)
    (hpower : BinaryArithmetic.toNat exponent ≤ W)
    (hcount : CounterPrograms.value counter ≤ W) :
    SubexpLagrangeCacheRow.budget D B i exponent counter ≤ 8000000 * (W + 1)^6 :=
  (row_budget_le_majorant D B i W exponent counter hD hB hi he hc hpower hcount).trans
    (rowMajorant_le W)

theorem budgetSum_le (D B start fuel W : ℕ) (exponent counter : List Bool)
    (hD : D ≤ W) (hB : B ≤ W) (hstop : start + fuel ≤ W)
    (he : exponent.length ≤ W) (hc : counter.length ≤ W)
    (hpower : BinaryArithmetic.toNat exponent ≤ W)
    (hcount : CounterPrograms.value counter ≤ W) :
    CounterForPrograms.budgetSum
      (fun i => SubexpLagrangeCacheRow.budget D B i exponent counter) start fuel ≤
      fuel * (8000000 * (W + 1)^6) := by
  apply CounterForPrograms.budgetSum_le
  intro i _ hhigh
  exact row_budget_le D B i W exponent counter hD hB (by omega) he hc hpower hcount

theorem row_budgetSum_le (p B W : ℕ) (exponent counter : List Bool)
    (hp : p ≤ W) (hB : B ≤ W)
    (he : exponent.length ≤ W) (hc : counter.length ≤ W)
    (hpower : BinaryArithmetic.toNat exponent ≤ W)
    (hcount : CounterPrograms.value counter ≤ W) :
    CounterForPrograms.budgetSum
      (fun i => SubexpLagrangeCacheRow.budget p B i exponent counter) 0 p ≤
      8000000 * (W + 1)^7 := by
  calc
    _ ≤ p * (8000000 * (W + 1)^6) :=
      budgetSum_le p B 0 p W exponent counter hp hB (by omega) he hc hpower hcount
    _ ≤ (W + 1) * (8000000 * (W + 1)^6) := by gcongr; omega
    _ = _ := by ring

/-- The exact outer-loop schedule, including all unary-loop tests. -/
def loopBound (p B : ℕ) (exponent counter : List Bool) : ℕ :=
  CounterForPrograms.budgetSum
    (fun i => SubexpLagrangeCacheRow.budget p B i exponent counter) 0 p + 2 * p + 2

theorem loopBound_le (p B W : ℕ) (exponent counter : List Bool)
    (hp : p ≤ W) (hB : B ≤ W)
    (he : exponent.length ≤ W) (hc : counter.length ≤ W)
    (hpower : BinaryArithmetic.toNat exponent ≤ W)
    (hcount : CounterPrograms.value counter ≤ W) :
    loopBound p B exponent counter ≤ 8000000 * (W + 1)^7 + 2 * p + 2 := by
  unfold loopBound
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (row_budgetSum_le p B W exponent counter hp hB he hc hpower hcount)
      (2 * p)) 2

/-- Bytes in the framed p-by-p cache of four-word coefficients. -/
def cacheSize (p B : ℕ) : ℕ := p * (2 * (p * (8 * B + 2) + 1) + 2) + 1

/-- Preparation, all rows, physical record reversal, and final cleanup. -/
def exactBound (x : Inputs) (B : ℕ) : ℕ :=
  SubexpLagrangeCachePreparation.runtimeBound x +
    loopBound (primeValue x) B x.exponent x.precision +
    (16 * cacheSize (primeValue x) B + 8) +
    (8 * B + 2 * primeValue x + 100 * (primeValue x + 1) * (inputLength x + 1))

def runtimeBound (x : Inputs) : ℕ :=
  100000000 * (1 + primeValue x + CounterPrograms.value x.precision +
    BinaryArithmetic.toNat x.exponent + inputLength x)^8

/-- The final one also pays for the compiled program's halt instruction. -/
theorem exactBound_add_one_le_runtimeBound (x : Inputs) (B : ℕ)
    (hB : B ≤ inputLength x) : exactBound x B + 1 ≤ runtimeBound x := by
  let W := primeValue x + CounterPrograms.value x.precision +
    BinaryArithmetic.toNat x.exponent + inputLength x
  have hp : primeValue x ≤ W := by dsimp [W]; omega
  have hL : inputLength x ≤ W := by dsimp [W]; omega
  have hBW : B ≤ W := hB.trans hL
  have he : x.exponent.length ≤ W := by
    have h : x.exponent.length ≤ inputLength x := by unfold inputLength; omega
    exact h.trans hL
  have hc : x.precision.length ≤ W := by
    have h : x.precision.length ≤ inputLength x := by unfold inputLength; omega
    exact h.trans hL
  have hpower : BinaryArithmetic.toNat x.exponent ≤ W := by dsimp [W]; omega
  have hcount : CounterPrograms.value x.precision ≤ W := by dsimp [W]; omega
  have hlo := loopBound_le (primeValue x) B W x.exponent x.precision
    hp hBW he hc hpower hcount
  have hlo' : loopBound (primeValue x) B x.exponent x.precision ≤
      8000000 * (W + 1)^7 + 2 * W + 2 := by omega
  have hprep : SubexpLagrangeCachePreparation.runtimeBound x ≤
      200 * (W + 1) * (W + 1) := by
    unfold SubexpLagrangeCachePreparation.runtimeBound
    gcongr
  have hcache : cacheSize (primeValue x) B ≤ cacheSize W W := by
    unfold cacheSize
    gcongr
  have hclean : 8 * B + 2 * primeValue x +
      100 * (primeValue x + 1) * (inputLength x + 1) ≤
      8 * W + 2 * W + 100 * (W + 1) * (W + 1) := by gcongr
  calc
    exactBound x B + 1 ≤
        200 * (W + 1) * (W + 1) + (8000000 * (W + 1)^7 + 2 * W + 2) +
        (16 * cacheSize W W + 8) +
        (8 * W + 2 * W + 100 * (W + 1) * (W + 1)) + 1 := by
      unfold exactBound
      omega
    _ ≤ 100000000 * (W + 1)^8 := by
      unfold cacheSize
      ring_nf
      omega
    _ = runtimeBound x := by unfold runtimeBound; dsimp only [W]; ring

theorem exactBound_le_runtimeBound (x : Inputs) (B : ℕ)
    (hB : B ≤ inputLength x) : exactBound x B ≤ runtimeBound x :=
  (Nat.le_succ _).trans (exactBound_add_one_le_runtimeBound x B hB)

end SubexponentialSAT.SubexpLagrangeCacheCost

end OAI.Algorithms
