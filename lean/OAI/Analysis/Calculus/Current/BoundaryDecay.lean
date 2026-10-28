import OAI.Analysis.Calculus.Current.Quantitative

/-! Uniform Gaussian decay of the smoothed wave term on the lateral boundary. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion _root_.MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise

theorem fiber_ratio_coordinate_le_one {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (hr : fiberDefining (1 / 10) a z ≤ 0) (i : Fin d) : ‖ratio z i‖ ≤ 1 := by
  have hs := fiber_ratio_bound (1 / 10) a z (by norm_num) hr
  have hi : ‖ratio z i‖ ^ 2 ≤ ∑ j, ‖ratio z j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖ratio z j‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg (ratio z i)]

theorem velocity_coordinate_le_one {d : ℕ} (v : Fin d → ℝ)
    (hv : (∑ i, |v i| ^ 2) ≤ 1 / 1600) (i : Fin d) : |v i| ≤ 1 := by
  have hi : |v i| ^ 2 ≤ ∑ j, |v j| ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg |v j|) (Finset.mem_univ i)
  nlinarith [abs_nonneg (v i)]

theorem waveCurrent_lateral_norm_le {d : ℕ} {ι : Type*} [Fintype ι]
    (a R C k : ℝ) (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hκ : ∀ j, 0 < κ j) (hk : ∀ j, k ≤ κ j)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0)
    (hR : ∀ j, κ j / ‖z none‖ ≤ R) (hC : ∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C)
    (hv : ∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600)
    (hr : fiberDefining (1 / 10) a z = 0)
    (hg : phaseCutoff (phi z / (a : ℂ)) ≠ 0) :
    ‖waveCurrent κ cR cI v x z‖ ≤ ((Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      (R ^ ((d : ℝ) / 2) * Real.exp (-(k * ‖z none‖ / 3200)) * C)) ^ 2 := by
  apply waveCurrent_norm_le_parameters κ cR cI v R C (k * ‖z none‖ / 3200)
    hκ hR0 hC0 x z hY hR hC
    (fun j i => velocity_coordinate_le_one (v j) (hv j) i)
    (fiber_ratio_coordinate_le_one a z hr.le)
  intro j
  have hj := hκ j
  have hd := lateral_squaredDistance_lower a z hr hg (v j) (hv j)
  have h₁ := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ κ j * ‖z none‖ / 2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_right (hk j) (show 0 ≤ ‖z none‖ / 3200 by positivity)
  nlinarith

theorem cutoffCurrent_norm_le {d : ℕ} (a : ℝ)
    (A : (Index d → ℝ) → (Index d → ℂ) → Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q)
    (x : Index d → ℝ) (z : Index d → ℂ) :
    ‖cutoffCurrent phaseCutoff a A x z‖ ≤ ‖A x z‖ := by
  change ‖phaseCutoff (phi z / (a : ℂ)) • A x z‖ ≤ ‖A x z‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (phaseCutoff_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (phaseCutoff_le_one _)

def sourceWavePart {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) : Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q :=
  cutoffCurrent phaseCutoff a
    (averagedWaveCurrent (periodizedKernelMeasure d h) cubeSpatialShift κ cR cI v) x z

theorem sourceWavePart_lateral_norm_le {d : ℕ} {ι : Type*} [Fintype ι]
    (h a R C k : ℝ) (hh : 0 < h) (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hκ : ∀ j, 0 < κ j) (hk : ∀ j, k ≤ κ j)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0)
    (hR : ∀ j, κ j / ‖z none‖ ≤ R) (hC : ∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C)
    (hv : ∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600)
    (hr : fiberDefining (1 / 10) a z = 0) :
    ‖sourceWavePart h a κ cR cI v x z‖ ≤ ((Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      (R ^ ((d : ℝ) / 2) * Real.exp (-(k * ‖z none‖ / 3200)) * C)) ^ 2 := by
  by_cases hg : phaseCutoff (phi z / (a : ℂ)) = 0
  · simp only [sourceWavePart, cutoffCurrent, hg, zero_smul, norm_zero]
    positivity
  let := periodizedKernelMeasure_isProbability d h hh
  apply (cutoffCurrent_norm_le a _ x z).trans
  have hn := norm_integral_le_of_norm_le_const (μ := periodizedKernelMeasure d h)
    (Filter.Eventually.of_forall fun t => waveCurrent_lateral_norm_le a R C k hR0 hC0
      κ cR cI v hκ hk (x + cubeSpatialShift t) z hY hR hC hv hr hg)
  simpa [averagedWaveCurrent, measureReal_def] using! hn

theorem exp_neg_le_rpow_of_log_bound (h s A : ℝ) (hh : 0 < h)
    (hA : s * Real.log h⁻¹ ≤ A) : Real.exp (-A) ≤ h ^ s := by
  rw [Real.rpow_def_of_pos hh]
  apply Real.exp_le_exp.mpr
  rw [Real.log_inv] at hA
  nlinarith

/-- Polynomial losses are absorbed by the explicit logarithmic Gaussian gain. -/
theorem sourceWavePart_lateral_power_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (h a R C k b M : ℝ) (hh : 0 < h) (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hκ : ∀ j, 0 < κ j) (hk : ∀ j, k ≤ κ j)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0)
    (hR : ∀ j, κ j / ‖z none‖ ≤ R) (hC : ∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C)
    (hv : ∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600)
    (hr : fiberDefining (1 / 10) a z = 0)
    (hpoly : (Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      (R ^ ((d : ℝ) / 2) * C) ≤ h ^ (-b))
    (hlog : (b + M / 2) * Real.log h⁻¹ ≤ k * ‖z none‖ / 3200) :
    ‖sourceWavePart h a κ cR cI v x z‖ ≤ h ^ M := by
  have he := exp_neg_le_rpow_of_log_bound h (b + M / 2) _ hh hlog
  have hnonneg : 0 ≤ (Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      (R ^ ((d : ℝ) / 2) * C) := by positivity
  have hp := mul_le_mul hpoly he (Real.exp_nonneg _) (Real.rpow_nonneg hh.le _)
  have hpow : h ^ (-b) * h ^ (b + M / 2) = h ^ (M / 2) := by
    rw [← Real.rpow_add hh]
    congr 1
    ring
  rw [hpow] at hp
  have hsq := pow_le_pow_left₀ (mul_nonneg hnonneg (Real.exp_nonneg _)) hp 2
  have hsqpow : (h ^ (M / 2)) ^ 2 = h ^ M := by
    rw [pow_two, ← Real.rpow_add hh]
    congr 1
    ring
  rw [hsqpow] at hsq
  refine (sourceWavePart_lateral_norm_le h a R C k hh hR0 hC0
    κ cR cI v hκ hk x z hY hR hC hv hr).trans ?_
  convert hsq using 1 ; ring

end OAI.Analysis.Calculus.Current
