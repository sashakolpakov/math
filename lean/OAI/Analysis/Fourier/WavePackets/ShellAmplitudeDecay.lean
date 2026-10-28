import OAI.Analysis.Fourier.WavePackets.ShellAmplitude

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory Set FourierTransform
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def amplitudeShellFunction (A : ℝ × E → ℂ) (φ : SchwartzMap ℝ ℂ)
    (r δ : ℝ) (ξ : E) : ℂ := A (r, ξ) * φ ((r - ‖ξ‖) / δ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem amplitudeShellFunction_support (A : ℝ × E → ℂ)
    (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (r δ : ℝ) :
    tsupport (amplitudeShellFunction A φ r δ) ⊆ Prod.snd '' tsupport A := by
  apply closure_minimal _ (hc.image continuous_snd).isClosed
  intro ξ hξ
  refine ⟨(r, ξ), subset_tsupport A ?_, rfl⟩
  intro hz
  exact hξ (by simp [amplitudeShellFunction, hz])

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasCompactSupport_amplitudeShellFunction {A : ℝ × E → ℂ}
    (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (r δ : ℝ) :
    HasCompactSupport (amplitudeShellFunction A φ r δ) :=
  (hc.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
    (amplitudeShellFunction_support A hc φ r δ)

omit [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_amplitudeShellFunction {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hz : ∀ r : ℝ, (r, (0 : E)) ∉ tsupport A)
    (φ : SchwartzMap ℝ ℂ) (r δ : ℝ) : ContDiff ℝ ∞ (amplitudeShellFunction A φ r δ) := by
  have hAr : ContDiff ℝ ∞ (fun ξ : E => A (r, ξ)) := ha.comp (contDiff_const.prodMk contDiff_id)
  have hzAr : (0 : E) ∉ tsupport (fun ξ : E => A (r, ξ)) := by
    intro hn
    exact hz r (tsupport_comp_subset_preimage A (continuous_const.prodMk continuous_id) hn)
  have he : amplitudeShellFunction A φ r δ =
      annularShellSymbol (fun ξ => A (r, ξ)) φ r δ := by
    funext ξ
    exact mul_comm _ _
  rw [he]
  exact contDiff_annularShellSymbol hAr (hasCompactSupport_space_slice hc r) hzAr φ r δ

noncomputable def amplitudeShellSchwartz {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hz : ∀ r : ℝ, (r, (0 : E)) ∉ tsupport A)
    (φ : SchwartzMap ℝ ℂ) (r δ : ℝ) : SchwartzMap E ℂ :=
  (hasCompactSupport_amplitudeShellFunction hc φ r δ).toSchwartzMap
    (contDiff_amplitudeShellFunction ha hc hz φ r δ)

omit [MeasurableSpace E] [BorelSpace E] in
theorem uniform_amplitudeShell_seminorm_bound {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hz : ∀ r : ℝ, (r, (0 : E)) ∉ tsupport A)
    (φ : SchwartzMap ℝ ℂ) (k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r δ : ℝ, 0 < δ → δ ≤ 1 →
      SchwartzMap.seminorm ℝ k N (amplitudeShellSchwartz ha hc hz φ r δ) ≤ C * (δ⁻¹) ^ N := by
  obtain ⟨D, hD, hbnd⟩ := uniform_amplitude_shell_derivative_bound ha hc hz φ N
  obtain ⟨R, hR, hRS⟩ := (hc.image continuous_snd).isBounded.exists_pos_norm_le
  refine ⟨R ^ k * D, by positivity, ?_⟩
  intro r δ hδ hδone
  apply SchwartzMap.seminorm_le_bound _ _ _ _ (by positivity)
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (amplitudeShellFunction A φ r δ) x‖ ≤ _
  by_cases hx : x ∈ Prod.snd '' tsupport A
  · calc
      _ ≤ R ^ k * (D * (δ⁻¹) ^ N) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hRS x hx) k)
          (hbnd r δ hδ hδone x) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hzD : iteratedFDeriv ℝ N (amplitudeShellFunction A φ r δ) x = 0 := by
      by_contra hn
      exact hx (amplitudeShellFunction_support A hc φ r δ (support_iteratedFDeriv_subset N hn))
    rw [hzD, norm_zero, mul_zero]
    positivity

omit [MeasurableSpace E] [BorelSpace E] in
theorem uniform_amplitudeShell_finite_seminorm_bound {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hz : ∀ r : ℝ, (r, (0 : E)) ∉ tsupport A)
    (φ : SchwartzMap ℝ ℂ) (s : Finset (ℕ × ℕ)) :
    ∃ Q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ r δ : ℝ, 0 < δ → δ ≤ 1 →
      s.sup (schwartzSeminormFamily ℝ E ℂ) (amplitudeShellSchwartz ha hc hz φ r δ) ≤
        C * (δ⁻¹) ^ Q := by
  choose C hC hbnd using fun m : ℕ × ℕ => uniform_amplitudeShell_seminorm_bound ha hc hz φ m.1 m.2
  refine ⟨s.sup Prod.snd, ∑ m ∈ s, C m, Finset.sum_nonneg (fun m _ => hC m), ?_⟩
  intro r δ hδ hδone
  calc
    _ ≤ ∑ m ∈ s, schwartzSeminormFamily ℝ E ℂ m (amplitudeShellSchwartz ha hc hz φ r δ) := by
      have h := (Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℝ E ℂ) s)
        (amplitudeShellSchwartz ha hc hz φ r δ)
      change _ ≤ FunLike.coeAddMonoidHom _ _ _ (∑ m ∈ s, schwartzSeminormFamily ℝ E ℂ m)
        (amplitudeShellSchwartz ha hc hz φ r δ) at h
      simp only [map_sum, Finset.sum_apply] at h
      convert h using 1
      congr 1
    _ ≤ ∑ m ∈ s, C m * (δ⁻¹) ^ (s.sup Prod.snd) := by
      apply Finset.sum_le_sum
      intro m hm
      exact (hbnd m r δ hδ hδone).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ ((one_le_inv₀ hδ).2 hδone) (Finset.le_sup hm)) (hC m))
    _ = _ := by rw [Finset.sum_mul]

theorem uniform_amplitudeShell_inverse_decay {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hz : ∀ r : ℝ, (r, (0 : E)) ∉ tsupport A)
    (φ : SchwartzMap ℝ ℂ) (q : ℕ) :
    ∃ Q : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ r δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : E,
      ‖𝓕⁻ (amplitudeShellFunction A φ r δ) x‖ ≤
        C * (δ⁻¹) ^ Q * (1 + ‖x‖) ^ (-(q : ℝ)) ∧
      ‖fderiv ℝ (𝓕⁻ (amplitudeShellFunction A φ r δ)) x‖ ≤
        C * (δ⁻¹) ^ Q * (1 + ‖x‖) ^ (-(q : ℝ)) := by
  let p := schwartzSeminormFamily ℝ E ℂ
  let t : Seminorm ℝ (SchwartzMap E ℂ) := (Finset.Iic (q, 1)).sup p
  let F := fourierInvCLM ℝ (SchwartzMap E ℂ)
  have ht : Continuous t := Seminorm.continuous_finsetSup fun m _ =>
    (schwartz_withSeminorms ℝ E ℂ).continuous_seminorm m
  have htF : Continuous (t.comp F.toLinearMap) := ht.comp F.continuous
  obtain ⟨s, B, _, hB⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ E ℂ) (t.comp F.toLinearMap) htF
  obtain ⟨Q, D, hD, hDb⟩ := uniform_amplitudeShell_finite_seminorm_bound ha hc hz φ s
  let C := 2 ^ q * (B : ℝ) * D + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨Q, C, hC, ?_⟩
  intro r δ hδ hδone x
  let f := amplitudeShellSchwartz ha hc hz φ r δ
  let K : SchwartzMap E ℂ := 𝓕⁻ f
  have htK : t K ≤ (B : ℝ) * D * (δ⁻¹) ^ Q := by
    calc
      _ ≤ (B : ℝ) * s.sup p f := hB f
      _ ≤ (B : ℝ) * (D * (δ⁻¹) ^ Q) :=
        mul_le_mul_of_nonneg_left (hDb r δ hδ hδone) B.coe_nonneg
      _ = _ := by ring
  have hbound (j : ℕ) (hj : j ≤ 1) :
      ‖iteratedFDeriv ℝ j K x‖ ≤ C * (δ⁻¹) ^ Q * (1 + ‖x‖) ^ (-(q : ℝ)) := by
    have hx : 0 < 1 + ‖x‖ := by positivity
    rw [Real.rpow_neg hx.le, Real.rpow_natCast, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos hx q)).mpr
    calc
      _ = (1 + ‖x‖) ^ q * ‖iteratedFDeriv ℝ j K x‖ := by ring
      _ ≤ 2 ^ q * t K :=
        SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (q, 1)) le_rfl hj K x
      _ ≤ 2 ^ q * ((B : ℝ) * D * (δ⁻¹) ^ Q) :=
        mul_le_mul_of_nonneg_left htK (by positivity)
      _ ≤ C * (δ⁻¹) ^ Q := by dsimp [C]; nlinarith [pow_nonneg (inv_nonneg.mpr hδ.le) Q]
  have he : (K : E → ℂ) = 𝓕⁻ (amplitudeShellFunction A φ r δ) := SchwartzMap.fourierInv_coe f
  rw [← he]
  constructor
  · simpa using hbound 0 (by omega)
  · simpa only [norm_iteratedFDeriv_one] using hbound 1 le_rfl

end OAI.Analysis.Fourier.WavePackets
