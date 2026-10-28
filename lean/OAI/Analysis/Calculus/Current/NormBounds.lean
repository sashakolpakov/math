import OAI.Analysis.Calculus.Current.AmplitudeBounds
import OAI.Analysis.Calculus.Current.SourceProperties

/-! Quantitative norm bounds retain all Gaussian localization factors. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion _root_.MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise

theorem currentColumn_norm_le {d : ℕ} {ι : Type*} [Fintype ι]
    (W : Fin d → ℂ) (v : ι → Fin d → ℂ) (a : ι → OAI.Analysis.Calculus.Quaternion.Q) :
    ‖currentColumn W v a‖ ≤ ∑ j, ‖tangentVector (v j) W‖ * ‖a j‖ := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro i
  calc
    ‖currentColumn W v a i‖ ≤ ∑ j, ‖complexK (tangentVector (v j) W i) * star (a j)‖ :=
      norm_sum_le _ _
    _ = ∑ j, ‖tangentVector (v j) W i‖ * ‖a j‖ := by
      simp only [norm_mul, complexK_norm, Quaternion.norm_star]
    _ ≤ _ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (norm_le_pi_norm _ i) (norm_nonneg _)

theorem outer_norm_le {m : Type*} [Fintype m] (u : m → OAI.Analysis.Calculus.Quaternion.Q) :
    ‖OAI.Analysis.Calculus.Quaternion.outer u‖ ≤ ‖u‖ ^ 2 := by
  apply (pi_norm_le_iff_of_nonneg (sq_nonneg ‖u‖)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (sq_nonneg ‖u‖)).mpr
  intro j
  simp only [OAI.Analysis.Calculus.Quaternion.outer, norm_mul, Quaternion.norm_star, pow_two]
  exact mul_le_mul (norm_le_pi_norm _ i) (norm_le_pi_norm _ j) (norm_nonneg _) (norm_nonneg _)

theorem currentMatrix_norm_le {d : ℕ} {ι : Type*} [Fintype ι]
    (W : Fin d → ℂ) (v : ι → Fin d → ℂ) (a : ι → OAI.Analysis.Calculus.Quaternion.Q) :
    ‖currentMatrix W v a‖ ≤ (∑ j, ‖tangentVector (v j) W‖ * ‖a j‖) ^ 2 := by
  exact (outer_norm_le _).trans (pow_le_pow_left₀ (norm_nonneg _) (currentColumn_norm_le W v a) 2)

def gaussianModeSize {d : ℕ} (κ cR cI : ℝ) (v : Fin d → ℝ) (z : Index d → ℂ) : ℝ :=
  ((κ / ‖z none‖) ^ ((d : ℝ) / 2) *
    Real.exp (-κ * ‖z none‖ / 2 * squaredDistance (ratio z) v)) * ‖(⟨cR, cI⟩ : ℂ)‖

def gaussianCurrentMajorant {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (z : Index d → ℂ) : ℝ :=
  ∑ j, ‖tangentVector (fun i => (v j i : ℂ)) (ratio z)‖ *
    gaussianModeSize (κ j) (cR j) (cI j) (v j) z

theorem waveCurrent_norm_le_gaussian {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ j, 0 < κ j)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) :
    ‖waveCurrent κ cR cI v x z‖ ≤ gaussianCurrentMajorant κ cR cI v z ^ 2 := by
  have hn := currentMatrix_norm_le (ratio z) (fun j i => (v j i : ℂ))
    (fun j => normalizedModeAmplitude (κ j) (cR j) (cI j) (v j) x z)
  simpa only [waveCurrent, gaussianCurrentMajorant, gaussianModeSize,
    normalizedModeAmplitude_norm _ _ _ (hκ _) _ _ _ hY] using! hn

theorem averagedWaveCurrent_norm_le_gaussian {d : ℕ} {ι α : Type*} [Fintype ι]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (shift : α → Index d → ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hκ : ∀ j, 0 < κ j) (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) :
    ‖averagedWaveCurrent μ shift κ cR cI v x z‖ ≤ gaussianCurrentMajorant κ cR cI v z ^ 2 := by
  have hn := norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall fun t => waveCurrent_norm_le_gaussian κ cR cI v hκ (x + shift t) z hY)
  simpa [averagedWaveCurrent, measureReal_def] using! hn

end OAI.Analysis.Calculus.Current
