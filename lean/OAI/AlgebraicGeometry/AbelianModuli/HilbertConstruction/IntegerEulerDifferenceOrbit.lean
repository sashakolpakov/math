import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EulerShifts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassGroup
import Mathlib.Algebra.Group.ForwardDiff

/-! # Integer Euler Difference Orbit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegerEulerDifferenceOrbit

noncomputable section

/-! Tensor differences along powers of a line-bundle class are the
ordinary forward differences of its actual integer Euler orbit. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem lineBundleEulerDifference_power_orbit {X : Scheme.{u}}
    (a : Line.Bundles.LineBundle.IsoClass X) (f : Line.Bundles.LineBundle.IsoClass X → ℤ) (d : ℤ) (n : ℕ) (z : ℤ) :
    ((LineBundle.EulerShifts.lineBundleEulerShift X (a ^ d) - 1) ^ n) f (a ^ z) =
      (fwdDiff d)^[n] (fun w : ℤ => f (a ^ w)) z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Function.iterate_succ_apply']
    change ((LineBundle.EulerShifts.lineBundleEulerShift X (a ^ d) - 1) ^ n) f (a ^ z * a ^ d) -
        ((LineBundle.EulerShifts.lineBundleEulerShift X (a ^ d) - 1) ^ n) f (a ^ z) =
      (fwdDiff d)^[n] (fun w : ℤ => f (a ^ w)) (z + d) -
        (fwdDiff d)^[n] (fun w : ℤ => f (a ^ w)) z
    rw [← zpow_add, ih, ih]

theorem lineBundleEulerDifference_mixed_orbit {X : Scheme.{u}}
    (a : Line.Bundles.LineBundle.IsoClass X) (f : Line.Bundles.LineBundle.IsoClass X → ℤ) (d : ℤ) (n : ℕ) :
    ((LineBundle.EulerShifts.lineBundleEulerShift X a - 1) * (LineBundle.EulerShifts.lineBundleEulerShift X (a ^ d) - 1) ^ n) f 1 =
      fwdDiff 1 ((fwdDiff d)^[n] (fun w : ℤ => f (a ^ w))) 0 := by
  have h₁ := lineBundleEulerDifference_power_orbit a f d n 1
  have h₀ := lineBundleEulerDifference_power_orbit a f d n 0
  change ((LineBundle.EulerShifts.lineBundleEulerShift X (a ^ d) - 1) ^ n) f (1 * a) -
      ((LineBundle.EulerShifts.lineBundleEulerShift X (a ^ d) - 1) ^ n) f 1 = _
  simp only [zpow_one] at h₁
  rw [one_mul, h₁]
  rw [zpow_zero] at h₀
  rw [h₀]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegerEulerDifferenceOrbit
