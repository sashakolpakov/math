import Mathlib

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

theorem shell_moment_power {N t k : ℝ} (hN : 0 < N) (ht : 0 < t)
    (hk : 0 ≤ k) (η a b p r : ℝ) :
    (η/N) * t^r * (k*N^a*t^b)^p =
      (η*k^p) * N^(a*p-1) * t^(r+b*p) := by
  rw [Real.mul_rpow (mul_nonneg hk (Real.rpow_nonneg hN.le a))
      (Real.rpow_nonneg ht.le b),
    Real.mul_rpow hk (Real.rpow_nonneg hN.le a),
    ← Real.rpow_mul hN.le, ← Real.rpow_mul ht.le,
    Real.rpow_sub hN, Real.rpow_one, Real.rpow_add ht]
  ring

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
