import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainAssembly
import OAI.Algorithms.SubexponentialSAT.SubexpMainCostAssembly

namespace OAI.Algorithms

/-!
# Cost of a complete sparse-record visit

The bound includes the record parser, empty-clause guard, actual backend
prefixSteps, singleton decoder, workspace cleanup, and leaf epilogue.
-/

namespace SubexponentialSAT.SubexpMainVisitBounds

open SubexpMainProgram SubexpComputation

theorem decoder_budget_le (width : ℕ) :
    SubexpH0CountDecision.budget width ≤ 501 * (width + 1) ^ 2 := by
  unfold SubexpH0CountDecision.budget
  nlinarith

theorem visit_le (er count width prefixSteps : ℕ) (bits : List Bool) :
    6 * bits.length +
      (SubexpLeafContract.leafBound er count width prefixSteps bits +
        200 * (bits.length + 1)) + 7 ≤
      3 * prefixSteps + 2000 * (bits.length + width + count + workRegs er + 1) ^ 2 := by
  let S := bits.length + width + count + workRegs er + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hself : S ≤ S ^ 2 := by nlinarith
  have hw : width + 1 ≤ S := by dsimp [S]; omega
  have hbudget : SubexpH0CountDecision.budget width ≤ 501 * S ^ 2 :=
    (decoder_budget_le width).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw 2))
  have hb : bits.length ≤ S := by dsimp [S]; omega
  have hc : count ≤ S := by dsimp [S]; omega
  have hr : workRegs er ≤ S := by dsimp [S]; omega
  change _ ≤ 3 * prefixSteps + 2000 * S ^ 2
  unfold SubexpLeafContract.leafBound
  nlinarith

/-- One envelope for the prefixSteps and its physical size parameters bounds a
complete record visit. The envelope need not bound the pending leaf stream. -/
theorem visit_envelope (er count width prefixSteps : ℕ) (bits : List Bool)
    {P : ℝ} (hP : 1 ≤ P) (hp : (prefixSteps : ℝ) ≤ P)
    (hb : (bits.length : ℝ) ≤ P) (hw : (width : ℝ) ≤ P)
    (hc : (count : ℝ) ≤ P) (hr : (workRegs er : ℝ) ≤ P) :
    ((6 * bits.length +
      (SubexpLeafContract.leafBound er count width prefixSteps bits +
        200 * (bits.length + 1)) + 7 : ℕ) : ℝ) ≤ 50003 * P ^ 2 := by
  have h := Nat.cast_le (α := ℝ).mpr (visit_le er count width prefixSteps bits)
  push_cast at h
  have hsize : (bits.length : ℝ) + width + count + workRegs er + 1 ≤ 5 * P := by
    linarith
  have hsize0 : 0 ≤ (bits.length : ℝ) + width + count + workRegs er + 1 := by
    positivity
  have hP0 : 0 ≤ P := by linarith
  have hsquare := pow_le_pow_left₀ hsize0 hsize 2
  have hself : P ≤ P ^ 2 := by nlinarith
  push_cast
  nlinarith

theorem visit_runtimeBound (er count n ell p : ℕ) (prefixLimit : List Bool → ℕ)
    (bits : List Bool) {C a : ℝ} {d L : ℕ} (hC : 1 ≤ C) (ha : 0 ≤ a)
    (hp : (prefixLimit bits : ℝ) ≤ runtimeBound C a d L n)
    (hb : (bits.length : ℝ) ≤ runtimeBound C a d L n)
    (hw : (SubexpLeafContract.wordWidth n ell p : ℝ) ≤ runtimeBound C a d L n)
    (hc : (count : ℝ) ≤ runtimeBound C a d L n)
    (hr : (workRegs er : ℝ) ≤ runtimeBound C a d L n) :
    ((6 * bits.length + SubexpMainAssembly.leafCost er count n ell p prefixLimit bits + 7 : ℕ) : ℝ) ≤
      runtimeBound (50003 * C ^ 2) (2 * a) (d * 2) L n := by
  calc
    _ ≤ 50003 * runtimeBound C a d L n ^ 2 :=
      visit_envelope er count (SubexpLeafContract.wordWidth n ell p) (prefixLimit bits)
        bits (one_le_runtimeBound hC ha d L n) hp hb hw hc hr
    _ = _ := by rw [runtimeBound_pow, ← runtimeBound_mul_constant]; norm_num

end SubexponentialSAT.SubexpMainVisitBounds

end OAI.Algorithms
