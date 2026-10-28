import OAI.Analysis.Calculus.Current.Crude

/-! Exact cancellation of the cofactor's lateral normal flux. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise

theorem fiberCofactor_normal_row_zero {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) : star (fiberGradient w a z) ᵥ* fiberCofactor w a z = 0 := by
  funext b
  have h := fiberCofactor_orthogonal_gradient w a z hY (Pi.single b 1)
  simpa [Matrix.mulVec_single_one, Matrix.vecMul, dotProduct] using h

theorem sourceRegularizedCurrent_normal_row {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) :
    star (fiberGradient (1 / 10) a z) ᵥ* sourceRegularizedCurrent h a κ cR cI v x z =
      star (fiberGradient (1 / 10) a z) ᵥ* sourceWavePart h a κ cR cI v x z := by
  change _ ᵥ* (sourceWavePart h a κ cR cI v x z +
    h ^ (50 * (d + 1)) • fiberCofactor (1 / 10) a z) = _
  rw [Matrix.vecMul_add, Matrix.vecMul_smul, fiberCofactor_normal_row_zero _ _ _ hY,
    smul_zero, add_zero]

theorem quaternion_vecMul_norm_le {ι ν : Type*} [Fintype ι] [Fintype ν]
    (u : ι → OAI.Analysis.Calculus.Quaternion.Q) (A : Matrix ι ν OAI.Analysis.Calculus.Quaternion.Q) :
    ‖u ᵥ* A‖ ≤ (Fintype.card ι : ℝ) * ‖u‖ * ‖A‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro b
  calc
    _ ≤ ∑ i, ‖u i * A i b‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖u‖ * ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm u i)
        ((norm_le_pi_norm _ b).trans (norm_le_pi_norm _ i)) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

theorem sourceRegularizedCurrent_normal_flux_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) :
    ‖star (fiberGradient (1 / 10) a z) ᵥ* sourceRegularizedCurrent h a κ cR cI v x z‖ ≤
      ((d : ℝ) + 2) * ‖fiberGradient (1 / 10) a z‖ * ‖sourceWavePart h a κ cR cI v x z‖ := by
  rw [sourceRegularizedCurrent_normal_row _ _ _ _ _ _ _ _ hY]
  simpa [Index, norm_star, add_assoc] using
    quaternion_vecMul_norm_le (star (fiberGradient (1 / 10) a z)) (sourceWavePart h a κ cR cI v x z)

theorem fiberMap_coordinate_norm_le_one {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hr : fiberDefining w a z ≤ 0) (i : Option (Fin d)) : ‖fiberMap w a z i‖ ≤ 1 := by
  have hi : ‖fiberMap w a z i‖ ^ 2 ≤ ∑ j, ‖fiberMap w a z j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖fiberMap w a z j‖) (Finset.mem_univ i)
  change (∑ j, ‖fiberMap w a z j‖ ^ 2) - 1 ≤ 0 at hr
  nlinarith [norm_nonneg (fiberMap w a z i)]

theorem fiberGradient_norm_le {d : ℕ} (a : ℝ) (ha : 0 < a)
    (z : Index d → ℂ) (hay : a ≤ ‖z none‖)
    (hr : fiberDefining (1 / 10) a z ≤ 0) :
    ‖fiberGradient (1 / 10) a z‖ ≤ 20 * ((d : ℝ) + 1) ^ 2 / a := by
  have hY : z none ≠ 0 := norm_pos_iff.mp (ha.trans_le hay)
  have hJ := quaternionFiberJacobian_norm_le a ha z hay hr
  have hqi : ‖qi‖ = 1 := by
    have hs : Quaternion.normSq qi = 1 := by norm_num [qi, Quaternion.normSq_def']
    rw [Quaternion.normSq_eq_norm_mul_self] at hs
    nlinarith [norm_nonneg qi]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro b
  have hv : ‖((quaternionFiberJacobian (1 / 10) a z)ᴴ *ᵥ
      (fun i => complexK (fiberMap (1 / 10) a z i))) b‖ ≤
      ((d : ℝ) + 1) * (10 * ((d : ℝ) + 1) / a) := by
    calc
      _ ≤ ∑ i, ‖star (quaternionFiberJacobian (1 / 10) a z i b) *
          complexK (fiberMap (1 / 10) a z i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Option (Fin d), 10 * ((d : ℝ) + 1) / a := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul, norm_star, complexK_norm]
        have hij := ((norm_le_pi_norm (quaternionFiberJacobian (1 / 10) a z i) b).trans
          (norm_le_pi_norm (quaternionFiberJacobian (1 / 10) a z) i)).trans hJ
        exact (mul_le_mul hij (fiberMap_coordinate_norm_le_one _ _ _ hr i)
          (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
      _ = _ := by simp [Fintype.card_option]
  rw [fiberGradient_formula _ _ _ hY, norm_smul, norm_mul, hqi]
  norm_num
  calc
    _ ≤ 2 * (((d : ℝ) + 1) * (10 * ((d : ℝ) + 1) / a)) := by linarith
    _ = _ := by ring

theorem sourceRegularizedCurrent_lateral_power_flux_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (h a R C k b M : ℝ) (hh : 0 < h) (hha : h ≤ a)
    (hR0 : 0 ≤ R) (hC0 : 0 ≤ C) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hκ : ∀ j, 0 < κ j) (hk : ∀ j, k ≤ κ j)
    (x : Index d → ℝ) (z : Index d → ℂ) (hay : a ≤ ‖z none‖)
    (hR : ∀ j, κ j / ‖z none‖ ≤ R) (hC : ∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C)
    (hv : ∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600)
    (hr : fiberDefining (1 / 10) a z = 0)
    (hpoly : (Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      (R ^ ((d : ℝ) / 2) * C) ≤ h ^ (-b))
    (hlog : (b + M / 2) * Real.log h⁻¹ ≤ k * ‖z none‖ / 3200) :
    ‖star (fiberGradient (1 / 10) a z) ᵥ* sourceRegularizedCurrent h a κ cR cI v x z‖ ≤
      (20 * ((d : ℝ) + 2) * ((d : ℝ) + 1) ^ 2) * h ^ (M - 1) := by
  have ha := hh.trans_le hha
  have hY : z none ≠ 0 := norm_pos_iff.mp (ha.trans_le hay)
  have hw := sourceWavePart_lateral_power_bound h a R C k b M hh hR0 hC0
    κ cR cI v hκ hk x z hY hR hC hv hr hpoly hlog
  have hg : ‖fiberGradient (1 / 10) a z‖ ≤ 20 * ((d : ℝ) + 1) ^ 2 / h :=
    (fiberGradient_norm_le a ha z hay hr.le).trans
      (div_le_div_of_nonneg_left (by positivity) hh hha)
  refine (sourceRegularizedCurrent_normal_flux_bound h a κ cR cI v x z hY).trans ?_
  have hp := mul_le_mul
    (mul_le_mul_of_nonneg_left hg (show 0 ≤ (d : ℝ) + 2 by positivity)) hw
    (norm_nonneg _) (by positivity)
  convert hp using 1
  rw [Real.rpow_sub hh, Real.rpow_one]
  ring

end OAI.Analysis.Calculus.Current
