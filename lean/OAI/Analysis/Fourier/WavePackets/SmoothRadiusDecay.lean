import OAI.Analysis.Fourier.WavePackets.ShellAmplitude
import OAI.Analysis.Fourier.SquareFunction.SmoothRadiusKernel

open OAI.Analysis.Fourier.Wave

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory FourierTransform Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def compactSliceSchwartz {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (r : ℝ) : SchwartzMap E ℂ :=
  (hasCompactSupport_space_slice hc r).toSchwartzMap
    (ha.comp (contDiff_const.prodMk contDiff_id))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem uniform_compactSlice_seminorm {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r,
      SchwartzMap.seminorm ℝ k N (compactSliceSchwartz ha hc r) ≤ C := by
  obtain ⟨D, hD, hb⟩ := hc.exists_bound_iteratedFDeriv ha N
  obtain ⟨R, hR, hRS⟩ := (hc.image continuous_snd).isBounded.exists_pos_norm_le
  let L := ContinuousLinearMap.inr ℝ ℝ E
  refine ⟨R ^ k * D * ‖L‖ ^ N, by positivity, ?_⟩
  intro r
  apply SchwartzMap.seminorm_le_bound _ _ _ _ (by positivity)
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (fun ξ => A (r, ξ)) x‖ ≤ _
  by_cases hx : x ∈ Prod.snd '' tsupport A
  · have hrest := norm_iteratedFDeriv_affine_restriction ha L (r, 0) N x
    have he : (fun y : E => A ((r, 0) + L y)) = (fun y => A (r, y)) := by
      funext y
      simp [L]
    rw [he] at hrest
    have hd : ‖iteratedFDeriv ℝ N (fun ξ => A (r, ξ)) x‖ ≤ D * ‖L‖ ^ N :=
      hrest.trans (mul_le_mul_of_nonneg_right (hb N le_rfl _) (by positivity))
    calc
      _ ≤ R ^ k * (D * ‖L‖ ^ N) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hRS x hx) k) hd
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hz : iteratedFDeriv ℝ N (fun ξ => A (r, ξ)) x = 0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset N hn
      have hs' := tsupport_comp_subset_preimage A (continuous_const.prodMk continuous_id) hs
      exact hx ⟨(r, x), hs', rfl⟩
    rw [hz, norm_zero, mul_zero]
    positivity

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem uniform_compactSlice_finite_seminorm {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (s : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r,
      s.sup (schwartzSeminormFamily ℝ E ℂ) (compactSliceSchwartz ha hc r) ≤ C := by
  choose C hC hb using fun m : ℕ × ℕ => uniform_compactSlice_seminorm ha hc m.1 m.2
  refine ⟨∑ m ∈ s, C m, Finset.sum_nonneg (fun m _ => hC m), ?_⟩
  intro r
  calc
    _ ≤ ∑ m ∈ s, schwartzSeminormFamily ℝ E ℂ m (compactSliceSchwartz ha hc r) := by
      have h := (Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℝ E ℂ) s)
        (compactSliceSchwartz ha hc r)
      change _ ≤ FunLike.coeAddMonoidHom _ _ _ (∑ m ∈ s, schwartzSeminormFamily ℝ E ℂ m)
        (compactSliceSchwartz ha hc r) at h
      simp only [map_sum, Finset.sum_apply] at h
      convert h using 1
      congr 1
    _ ≤ _ := Finset.sum_le_sum (fun m _ => hb m r)

theorem uniform_compactSlice_inverse_decay {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, ∀ x : E,
      ‖𝓕⁻ (fun ξ => A (r, ξ)) x‖ ≤ C * (1 + ‖x‖) ^ (-(q : ℝ)) ∧
      ‖fderiv ℝ (𝓕⁻ (fun ξ => A (r, ξ))) x‖ ≤ C * (1 + ‖x‖) ^ (-(q : ℝ)) := by
  let p := schwartzSeminormFamily ℝ E ℂ
  let t : Seminorm ℝ (SchwartzMap E ℂ) := (Finset.Iic (q, 1)).sup p
  let F := fourierInvCLM ℝ (SchwartzMap E ℂ)
  have ht : Continuous t := Seminorm.continuous_finsetSup fun m _ =>
    (schwartz_withSeminorms ℝ E ℂ).continuous_seminorm m
  have htF : Continuous (t.comp F.toLinearMap) := ht.comp F.continuous
  obtain ⟨s, B, _, hB⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ E ℂ) (t.comp F.toLinearMap) htF
  obtain ⟨D, hD, hDb⟩ := uniform_compactSlice_finite_seminorm ha hc s
  let C := 2 ^ q * (B : ℝ) * D + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro r x
  let f := compactSliceSchwartz ha hc r
  let K : SchwartzMap E ℂ := 𝓕⁻ f
  have htK : t K ≤ (B : ℝ) * D :=
    (hB f).trans (mul_le_mul_of_nonneg_left (hDb r) B.coe_nonneg)
  have hbound (j : ℕ) (hj : j ≤ 1) :
      ‖iteratedFDeriv ℝ j K x‖ ≤ C * (1 + ‖x‖) ^ (-(q : ℝ)) := by
    have hx : 0 < 1 + ‖x‖ := by positivity
    rw [Real.rpow_neg hx.le, Real.rpow_natCast, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos hx q)).mpr
    calc
      _ = (1 + ‖x‖) ^ q * ‖iteratedFDeriv ℝ j K x‖ := by ring
      _ ≤ 2 ^ q * t K :=
        SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (q, 1)) le_rfl hj K x
      _ ≤ 2 ^ q * ((B : ℝ) * D) := mul_le_mul_of_nonneg_left htK (by positivity)
      _ ≤ C := by dsimp [C]; ring_nf; linarith
  have he : (K : E → ℂ) = 𝓕⁻ (fun ξ => A (r, ξ)) := SchwartzMap.fourierInv_coe f
  rw [← he]
  exact ⟨by simpa using hbound 0 (by omega),
    by simpa only [norm_iteratedFDeriv_one] using hbound 1 le_rfl⟩

/-- Hilbert-valued smooth compact radius kernels and their spatial gradients
decay to arbitrary order, including when the symbol meets zero frequency. -/
theorem smoothRadiusKernel_decay {n : ℕ} {A : ℝ × Space n → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space n,
      ‖OAI.Analysis.Fourier.SquareFunction.smoothRadiusKernel A ha.continuous x‖ ≤ C * (1 + ‖x‖) ^ (-(q : ℝ)) ∧
      ‖fderiv ℝ (OAI.Analysis.Fourier.SquareFunction.smoothRadiusKernel A ha.continuous) x‖ ≤
        C * (1 + ‖x‖) ^ (-(q : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := uniform_compactSlice_inverse_decay ha hc q
  refine ⟨C, hC, ?_⟩
  intro x
  have hm := OAI.Analysis.Fourier.SquareFunction.continuous_smoothRadiusSymbol A ha.continuous
  have hmc := OAI.Analysis.Fourier.SquareFunction.hasCompactSupport_smoothRadiusSymbol A ha.continuous hc
  have hB : 0 ≤ C * (1 + ‖x‖) ^ (-(q : ℝ)) := by positivity
  constructor
  · apply OAI.Analysis.Fourier.SquareFunction.norm_radiusFourierKernel_le (hm.integrable_of_hasCompactSupport hmc) x hB
    intro r
    exact (hb r x).1
  · apply OAI.Analysis.Fourier.SquareFunction.norm_fderiv_radiusFourierKernel_le hm hmc x hB
    intro r
    exact (hb r x).2

end OAI.Analysis.Fourier.WavePackets
