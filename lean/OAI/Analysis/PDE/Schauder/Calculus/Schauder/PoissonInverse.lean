import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Poisson

/-! A normalized, genuine inverse of the Euclidean Laplacian on compact smooth data. -/

noncomputable section
open _root_.MeasureTheory Metric InnerProductSpace Laplacian
namespace OAI.Analysis.PDE.Schauder

def poissonNormalization (m : ℕ) : ℝ :=
  (m : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m)

theorem poissonNormalization_ne_zero {m : ℕ} (hm : 3 ≤ m) : poissonNormalization m ≠ 0 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hV : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne
  exact mul_ne_zero (mul_ne_zero (by linarith) hV.ne') (by linarith)

def poissonPotential {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) : EuclideanSpace ℝ (Fin m) → ℝ :=
  (poissonNormalization m)⁻¹ • newtonianPotential f

theorem contDiff_poissonPotential {m : ℕ} (hm : 1 ≤ m) {k : ℕ∞}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ k f) (hfc : HasCompactSupport f) :
    ContDiff ℝ k (poissonPotential f) := by
  simpa only [poissonPotential, Pi.smul_apply] using!
    (contDiff_newtonianPotential hm f hf hfc).const_smul (poissonNormalization m)⁻¹

theorem laplacian_poissonPotential {m : ℕ} (hm : 3 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin m)) :
    (laplacian (poissonPotential f) : EuclideanSpace ℝ (Fin m) → ℝ) x = f x := by
  rw [poissonPotential, laplacian_smul _
    (contDiff_newtonianPotential (show 1 ≤ m by omega) f hf hfc).contDiffAt,
    laplacian_newtonianPotential (show 2 ≤ m by omega) f hf hfc x]
  change (poissonNormalization m)⁻¹ * (poissonNormalization m * f x) = f x
  rw [← mul_assoc, inv_mul_cancel₀ (poissonNormalization_ne_zero hm), one_mul]

end OAI.Analysis.PDE.Schauder
