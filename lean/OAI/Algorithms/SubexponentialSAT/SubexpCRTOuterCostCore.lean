import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterFinish
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterCofactorView
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterNeg
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterHorner
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterAccumulate

namespace OAI.Algorithms

/-! Numerical bounds for the actual outer CRT schedule. The local, middle,
and controller formulas are identified definitionally with the execution
module in `SubexpCRTOuterCost`. Both the number represented by the Fermat
exponent and its stored bit length are charged here. -/

namespace SubexponentialSAT.SubexpCRTOuterCost

open SubexpCRTOuterProgram

def localBound (B D Q : ℕ) (exponent : List Bool) : ℕ :=
  SubexpQuarticPowerProgram.runtimeBound B exponent +
    5000000 * (Q + 1) * (D + 1)^4 * (B + 1)^2 + 3

def middleBound (B D Q : ℕ) (exponent : List Bool) : ℕ :=
  localBound B D Q exponent +
    SubexpCRTOuterCofactorView.uniformBudget B D Q +
    SubexpCRTOuterNeg.runtimeBound B + SubexpCRTOuterHorner.budget D B +
    SubexpCRTOuterAccumulate.runtimeBound B

def commandBound (B D Q : ℕ) (exponent : List Bool) : ℕ :=
  controllerBudget B D Q (middleBound B D Q exponent)

def localMajorant (W : ℕ) : ℕ :=
  500000 * (W + 1)^3 + 5000000 * (W + 1)^7 + 3

def middleMajorant (W : ℕ) : ℕ :=
  localMajorant W + SubexpCRTOuterCofactorView.uniformBudget W W W +
    SubexpCRTOuterNeg.runtimeBound W + 800000 * (W + 1)^3 +
    SubexpCRTOuterAccumulate.runtimeBound W

/-- The final one is the compiled program's halt instruction. -/
def majorant (W : ℕ) : ℕ := controllerBudget W W W (middleMajorant W) + 1

theorem localBound_le (B D Q : ℕ) (exponent : List Bool) (W : ℕ)
    (hB : B ≤ W) (hD : D ≤ W) (hQ : Q ≤ W)
    (hE : exponent.length ≤ W) (hN : BinaryArithmetic.toNat exponent ≤ W) :
    localBound B D Q exponent ≤ localMajorant W := by
  have hp := SubexpQuarticPowerProgram.runtimeBound_le B exponent W hB hE hN
  unfold localBound
  calc
    _ ≤ 500000 * (W + 1)^3 +
        5000000 * (W + 1) * (W + 1)^4 * (W + 1)^2 + 3 := by
      gcongr
    _ = localMajorant W := by unfold localMajorant; ring

theorem middleBound_le (B D Q : ℕ) (exponent : List Bool) (W : ℕ)
    (hB : B ≤ W) (hD : D ≤ W) (hQ : Q ≤ W)
    (hE : exponent.length ≤ W) (hN : BinaryArithmetic.toNat exponent ≤ W) :
    middleBound B D Q exponent ≤ middleMajorant W := by
  have hl := localBound_le B D Q exponent W hB hD hQ hE hN
  have hc : SubexpCRTOuterCofactorView.uniformBudget B D Q ≤
      SubexpCRTOuterCofactorView.uniformBudget W W W := by
    unfold SubexpCRTOuterCofactorView.uniformBudget SubexpCRTCofactorMachine.polynomialBound
    gcongr
  have hn : SubexpCRTOuterNeg.runtimeBound B ≤ SubexpCRTOuterNeg.runtimeBound W := by
    unfold SubexpCRTOuterNeg.runtimeBound
    gcongr
  have hh : SubexpCRTOuterHorner.budget D B ≤ 800000 * (W + 1)^3 := by
    calc
      _ ≤ 800000 * (D + 1) * (B + 1)^2 := SubexpCRTOuterHorner.budget_le _ _
      _ ≤ 800000 * (W + 1) * (W + 1)^2 := by gcongr
      _ = _ := by ring
  have ha : SubexpCRTOuterAccumulate.runtimeBound B ≤
      SubexpCRTOuterAccumulate.runtimeBound W := by
    unfold SubexpCRTOuterAccumulate.runtimeBound SubexpCRTWeightedMachine.runtimeBound
    gcongr
  unfold middleBound middleMajorant
  omega

theorem controllerBudget_mono {B D Q K B' D' Q' K' : ℕ}
    (hB : B ≤ B') (hD : D ≤ D') (hQ : Q ≤ Q') (hK : K ≤ K') :
    controllerBudget B D Q K ≤ controllerBudget B' D' Q' K' := by
  unfold controllerBudget initializationBudget SubexpFactorCountSetup.countBudget
    transportCost cleanupBudget
  gcongr

theorem commandBound_le (B D Q : ℕ) (exponent : List Bool) (W : ℕ)
    (hB : B ≤ W) (hD : D ≤ W) (hQ : Q ≤ W)
    (hE : exponent.length ≤ W) (hN : BinaryArithmetic.toNat exponent ≤ W) :
    commandBound B D Q exponent + 1 ≤ majorant W := by
  exact Nat.add_le_add_right
    (controllerBudget_mono hB hD hQ (middleBound_le B D Q exponent W hB hD hQ hE hN)) 1

/-- Expanding only the measured cost formulas exhibits their fixed degree. -/
theorem majorant_eq (W : ℕ) :
    majorant W = 5000000 * W^8 + 35000000 * W^7 + 105000000 * W^6 +
      215500000 * W^5 + 228275000 * W^4 + 130501416 * W^3 +
      42575810 * W^2 + 6750243 * W + 79 := by
  unfold majorant middleMajorant localMajorant controllerBudget initializationBudget
    SubexpFactorCountSetup.countBudget transportCost cleanupBudget
    SubexpCRTOuterCofactorView.uniformBudget SubexpCRTCofactorMachine.polynomialBound
    SubexpCRTOuterNeg.runtimeBound SubexpCRTOuterAccumulate.runtimeBound
    SubexpCRTWeightedMachine.runtimeBound
  ring

theorem majorant_le_degree_eight (W : ℕ) : majorant W ≤ 800000000 * (W + 1)^8 := by
  have hp (n : ℕ) (hn : n ≤ 8) : W^n ≤ (W + 1)^8 :=
    (Nat.pow_le_pow_left (Nat.le_succ W) n).trans
      (Nat.pow_le_pow_right (Nat.succ_pos W) hn)
  have h0 := hp 0 (by decide)
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  simp only [pow_zero, pow_one] at h0 h1
  rw [majorant_eq]
  omega

/-- A bound with no supplied common cap: every varying input quantity is
included, in particular the numerical exponent and its representation length. -/
theorem commandBound_le_inputs (B D Q : ℕ) (exponent : List Bool) :
    commandBound B D Q exponent + 1 ≤
      800000000 * (B + D + Q + exponent.length + BinaryArithmetic.toNat exponent + 1)^8 := by
  let W := B + D + Q + exponent.length + BinaryArithmetic.toNat exponent
  have hb : commandBound B D Q exponent + 1 ≤ majorant W :=
    commandBound_le B D Q exponent W (by dsimp [W]; omega) (by dsimp [W]; omega)
      (by dsimp [W]; omega) (by dsimp [W]; omega) (by dsimp [W]; omega)
  exact hb.trans (majorant_le_degree_eight W)

end SubexponentialSAT.SubexpCRTOuterCost

end OAI.Algorithms
