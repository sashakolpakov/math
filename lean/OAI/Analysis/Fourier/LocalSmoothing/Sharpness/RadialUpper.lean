import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.RadialProfileFormula
import OAI.Analysis.Fourier.Radial.Sphere.Decay

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Filter Set
open scoped Topology ContDiff
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

theorem radialProfile_inverse_power_bound {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) {m : ℝ} (_ : 0 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v R : ℝ, 1 ≤ R → R ≤ |v| →
      ‖radialProfile g v‖ ≤ C * R^(-m) := by
  obtain ⟨C,hC,hb⟩ := radialProfile_polynomial_decay hg hc (Nat.ceil m)
  refine ⟨C,hC,fun v R hR hRv => ?_⟩
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hpow : R^m ≤ |v|^(Nat.ceil m) := by
    calc
      R^m ≤ R^((Nat.ceil m:ℕ):ℝ) := Real.rpow_le_rpow_of_exponent_le hR (Nat.le_ceil m)
      _ = R^(Nat.ceil m) := Real.rpow_natCast _ _
      _ ≤ |v|^(Nat.ceil m) := pow_le_pow_left₀ hRp.le hRv _
  have h := hb (-v)
  simp only [abs_neg,neg_neg] at h
  have hmul : R^m * ‖radialProfile g v‖ ≤ C :=
    (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans h
  rw [Real.rpow_neg hRp.le,← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hRp m)).mpr (by simpa only [mul_comm] using hmul)

theorem radialWave_spatial_bound {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∀ x : Space n,
      ‖radialWave n t x‖ ≤ C * (1+‖x‖)^(-radialOrder n) := by
  obtain ⟨C,hC,hdec⟩ := OAI.Analysis.Fourier.Radial.sphericalExtension_one_polynomial_decay hn
  have hm : 0 ≤ radialOrder n := by
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    unfold radialOrder
    linarith
  refine ⟨C * ∫ σ, ‖radialVolumeWeight n σ‖,
    mul_nonneg hC.le (integral_nonneg fun _ => norm_nonneg _),fun t x => ?_⟩
  have hb (σ : ℝ) :
      ‖(radialVolumeWeight n σ:ℂ) * phase (-t*σ) *
        OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n => (1:ℂ)) (σ•x)‖ ≤
      (C*(1+‖x‖)^(-radialOrder n)) * ‖radialVolumeWeight n σ‖ := by
    by_cases hz : radialVolumeWeight n σ = 0
    · simp [hz]
    · have hσ : 1 ≤ σ := (radialBump_support (subset_tsupport _
        (right_ne_zero_of_mul (show σ^(n-1)*radialBump σ ≠ 0 from hz)))).1
      have hσp : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
      have hnorm : ‖σ•x‖ = σ*‖x‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hσp]
      have hpow : (1+‖σ•x‖)^(-radialOrder n) ≤ (1+‖x‖)^(-radialOrder n) := by
        apply Real.rpow_le_rpow_of_nonpos (by positivity)
        · rw [hnorm]
          nlinarith [norm_nonneg x]
        · exact neg_nonpos.mpr hm
      have hd : ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n => (1:ℂ)) (σ•x)‖ ≤
          C*(1+‖x‖)^(-radialOrder n) := by
        have hd := hdec (σ•x)
        have he : -((n:ℝ)-1)/2 = -radialOrder n := by unfold radialOrder; ring
        rw [he] at hd
        exact hd.trans (mul_le_mul_of_nonneg_left hpow hC.le)
      simpa only [norm_mul,norm_phase,mul_one,one_mul,Complex.norm_real,mul_comm] using
        mul_le_mul_of_nonneg_left hd (norm_nonneg (radialVolumeWeight n σ))
  have h := norm_integral_le_of_norm_le
    ((radialVolumeWeight_integrable n).norm.const_mul (C*(1+‖x‖)^(-radialOrder n)))
    (Eventually.of_forall hb)
  change ‖radialWave n t x‖ ≤ _ at h
  rw [integral_const_mul] at h
  convert h using 1 ; ring

theorem radialWave_time_bound {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ |t| → ∀ x : Space n,
      ‖radialWave n t x‖ ≤ C * (|t|/2)^(-radialOrder n) := by
  have hm : 0 ≤ radialOrder n := by
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    unfold radialOrder
    linarith
  obtain ⟨C,hC,hspatial⟩ := radialWave_spatial_bound hn
  obtain ⟨D,hD,hprofile⟩ := radialProfile_inverse_power_bound
    (radialVolumeWeight_contDiff n) (radialVolumeWeight_hasCompactSupport n) hm
  let M := (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real univ
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  refine ⟨C+D*M,by positivity,fun t ht x => ?_⟩
  have hR : 1 ≤ |t|/2 := by linarith
  have hRp : 0 < |t|/2 := by linarith
  by_cases hx : |t|/2 ≤ ‖x‖
  · have hpow : (1+‖x‖)^(-radialOrder n) ≤ (|t|/2)^(-radialOrder n) :=
      Real.rpow_le_rpow_of_nonpos hRp (by linarith) (neg_nonpos.mpr hm)
    exact (hspatial t x).trans ((mul_le_mul_of_nonneg_left hpow hC).trans
      (mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg hRp.le _)))
  · have hpoint : ∀ᵐ v ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n,
        ‖radialProfile (radialVolumeWeight n) (inner ℝ x v-t)‖ ≤ D*(|t|/2)^(-radialOrder n) := by
      filter_upwards [OAI.MeasureTheory.Kakeya.ae_sphereMeasure_norm n] with v hv
      apply hprofile _ _ hR
      have hi := abs_real_inner_le_norm x v
      rw [hv,mul_one] at hi
      have hr := abs_sub_abs_le_abs_sub t (inner ℝ x v)
      rw [abs_sub_comm t] at hr
      linarith
    rw [radialWave_eq_sphere_profile]
    have h := norm_integral_le_of_norm_le_const hpoint
    change _ ≤ (D*(|t|/2)^(-radialOrder n))*M at h
    calc
      _ ≤ (D*M)*(|t|/2)^(-radialOrder n) := by convert h using 1 ; ring
      _ ≤ (C+D*M)*(|t|/2)^(-radialOrder n) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hRp.le _)

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
