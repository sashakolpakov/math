import OAI.Analysis.Fourier.WavePackets.ShellSchwartz

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory FourierTransform
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Quantitative decay of the actual thin-shell inverse Fourier kernel
and its spatial derivative. Any prescribed spatial decay is available
at the cost of a fixed polynomial in the reciprocal shell width. -/
theorem uniform_annularShell_inverse_decay {b : E → ℂ} (hb : ContDiff ℝ ∞ b)
    (hs : HasCompactSupport b) (hz : (0 : E) ∉ tsupport b)
    (φ : SchwartzMap ℝ ℂ) (q : ℕ) :
    ∃ Q : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ r δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : E,
      ‖𝓕⁻ (annularShellSymbol b φ r δ) x‖ ≤
        C * (δ⁻¹) ^ Q * (1 + ‖x‖) ^ (-(q : ℝ)) ∧
      ‖fderiv ℝ (𝓕⁻ (annularShellSymbol b φ r δ)) x‖ ≤
        C * (δ⁻¹) ^ Q * (1 + ‖x‖) ^ (-(q : ℝ)) := by
  let p := schwartzSeminormFamily ℝ E ℂ
  let t : Seminorm ℝ (SchwartzMap E ℂ) := (Finset.Iic (q, 1)).sup p
  let F := fourierInvCLM ℝ (SchwartzMap E ℂ)
  have ht : Continuous t := Seminorm.continuous_finsetSup fun m _ =>
    (schwartz_withSeminorms ℝ E ℂ).continuous_seminorm m
  have htF : Continuous (t.comp F.toLinearMap) := ht.comp F.continuous
  obtain ⟨s, A, _, hA⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ E ℂ) (t.comp F.toLinearMap) htF
  obtain ⟨Q, D, hD, hDb⟩ := uniform_annularShell_finite_seminorm_bound hb hs hz φ s
  let C := 2 ^ q * (A : ℝ) * D + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨Q, C, hC, ?_⟩
  intro r δ hδ hδone x
  let f := annularShellSchwartz hb hs hz φ r δ
  let K : SchwartzMap E ℂ := 𝓕⁻ f
  have htK : t K ≤ (A : ℝ) * D * (δ⁻¹) ^ Q := by
    calc
      _ ≤ (A : ℝ) * s.sup p f := hA f
      _ ≤ (A : ℝ) * (D * (δ⁻¹) ^ Q) :=
        mul_le_mul_of_nonneg_left (hDb r δ hδ hδone) A.coe_nonneg
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
      _ ≤ 2 ^ q * ((A : ℝ) * D * (δ⁻¹) ^ Q) :=
        mul_le_mul_of_nonneg_left htK (by positivity)
      _ ≤ C * (δ⁻¹) ^ Q := by dsimp [C]; nlinarith [pow_nonneg (inv_nonneg.mpr hδ.le) Q]
  have he : (K : E → ℂ) = 𝓕⁻ (annularShellSymbol b φ r δ) := by
    exact SchwartzMap.fourierInv_coe f
  rw [← he]
  constructor
  · simpa using hbound 0 (by omega)
  · simpa only [norm_iteratedFDeriv_one] using hbound 1 le_rfl

end OAI.Analysis.Fourier.WavePackets
