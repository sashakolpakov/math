import Mathlib.Tactic.Linarith
import Mathlib.Basic.Real.Basic

/-! # Three Energy Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ThreeEnergyBound

/-! Scalar aggregation of the three actual joint-energy component bounds. -/

theorem three_energy_component_bound (M C D n d s fn fd fs : ℝ)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hD : 0 ≤ D) (hn : 0 ≤ n) (hd : 0 ≤ d) (hs : 0 ≤ s)
    (hfn : fn ≤ M * n) (hfd : fd ≤ C * n + D * d) (hfs : fs ≤ C * n + D * s) :
    fn + fd + fs ≤ (M + 2 * C + D) * (n + d + s) := by
  have hmc : 0 ≤ M + 2 * C := add_nonneg hM (mul_nonneg (by norm_num) hC)
  nlinarith only [hfn, hfd, hfs, mul_nonneg hD hn, mul_nonneg hmc hd, mul_nonneg hmc hs]

end OAI.AlgebraicGeometry.DivisorClass.Chern.ThreeEnergyBound
