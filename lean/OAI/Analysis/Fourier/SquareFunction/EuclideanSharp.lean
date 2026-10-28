import OAI.Analysis.Fourier.SquareFunction.Oscillation

open OAI.Analysis.Fourier.Wave

/-! Transport of the sharp inequality to the Euclidean Fourier space. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set BoxIntegral
open scoped ENNReal

theorem setLIntegral_euclideanBox {n : ℕ} (g : Space n → ℝ≥0∞) (Q : Box (Fin n)) :
    (∫⁻ x in euclideanBox Q, g x) =
      ∫⁻ x in (Q : Set (Fin n → ℝ)), g (WithLp.toLp 2 x) := by
  simpa only [euclideanBox, WithLp.toLp_ofLp] using
    (PiLp.volume_preserving_ofLp (Fin n)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding
      (fun x => g (WithLp.toLp 2 x)) (Q : Set (Fin n → ℝ))

theorem positiveSetMean_euclideanBox {n : ℕ} (f : Space n → ℝ) (Q : Box (Fin n)) :
    positiveSetMean volume f (euclideanBox Q) =
      positiveSetMean volume (fun x => f (WithLp.toLp 2 x)) Q := by
  rw [positiveSetMean, positiveSetMean, setLIntegral_euclideanBox, volume_euclideanBox]

theorem setOscillation_euclideanBox {n : ℕ} (f : Space n → ℝ) (Q : Box (Fin n)) :
    setOscillation volume f (euclideanBox Q) =
      setOscillation volume (fun x => f (WithLp.toLp 2 x)) Q := by
  rw [setOscillation, setOscillation, positiveSetMean_euclideanBox,
    setLIntegral_euclideanBox, volume_euclideanBox]

/-- The global cube-oscillation norm estimate for the actual Euclidean space
on which the Fourier operators act. -/
theorem eLpNorm_le_of_euclidean_cube_oscillation {n : ℕ} [NeZero n]
    (f G : Space n → ℝ) (hfn : ∀ x, 0 ≤ f x) (hGn : ∀ x, 0 ≤ G x)
    (hfc : Continuous f) (hf : Integrable f) (hG : AEStronglyMeasurable G)
    {p γ : ℝ} (hp : 1 < p) (hγ : 0 < γ)
    (hsmall : γ * ((2 : ℝ) ^ n + 1) ^ p < 1)
    (hosc : ∀ Q : Box (Fin n), IsCubeBox Q → ∀ x ∈ euclideanBox Q,
      setOscillation volume f (euclideanBox Q) ≤ ENNReal.ofReal (G x)) :
    eLpNorm f (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal (1 / (1 - γ * ((2 : ℝ) ^ n + 1) ^ p))) ^ (1 / p) *
        ENNReal.ofReal (((2 : ℝ) ^ n + 1) / γ) *
          eLpNorm G (ENNReal.ofReal p) volume := by
  have h := eLpNorm_le_of_cube_oscillation
    (f ∘ WithLp.toLp 2) (G ∘ WithLp.toLp 2)
    (fun x => hfn _) (fun x => hGn _)
    (hfc.comp (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)))
    ((PiLp.volume_preserving_toLp (Fin n)).integrable_comp_of_integrable hf)
    (hG.comp_measurePreserving (PiLp.volume_preserving_toLp (Fin n)))
    hp hγ (by simpa only [Fintype.card_fin] using hsmall) ?_
  · rw [eLpNorm_comp_measurePreserving hfc.aestronglyMeasurable (PiLp.volume_preserving_toLp (Fin n)),
      eLpNorm_comp_measurePreserving hG (PiLp.volume_preserving_toLp (Fin n))] at h
    simpa only [Fintype.card_fin] using h
  · intro Q hQ x hx
    change setOscillation volume (fun x => f (WithLp.toLp 2 x)) Q ≤ _
    rw [← setOscillation_euclideanBox]
    exact hosc Q hQ (WithLp.toLp 2 x) hx

/-- The form used by the convolution decomposition: the comparison constant
may depend on the cube, and need not be the mean of the function. -/
theorem eLpNorm_le_of_euclidean_centered_oscillation {n : ℕ} [NeZero n]
    (f G : Space n → ℝ) (hfn : ∀ x, 0 ≤ f x) (hGn : ∀ x, 0 ≤ G x)
    (hfc : Continuous f) (hf : Integrable f) (hG : AEStronglyMeasurable G)
    {p γ : ℝ} (hp : 1 < p) (hγ : 0 < γ)
    (hsmall : γ * ((2 : ℝ) ^ n + 1) ^ p < 1)
    (hosc : ∀ Q : Box (Fin n), IsCubeBox Q → ∃ c : ℝ, ∀ x ∈ euclideanBox Q,
      (∫⁻ y in euclideanBox Q, ‖f y - c‖ₑ) / volume (euclideanBox Q) ≤ ENNReal.ofReal (G x)) :
    eLpNorm f (ENNReal.ofReal p) volume ≤
      2 * ((ENNReal.ofReal (1 / (1 - γ * ((2 : ℝ) ^ n + 1) ^ p))) ^ (1 / p) *
        ENNReal.ofReal (((2 : ℝ) ^ n + 1) / γ)) *
          eLpNorm G (ENNReal.ofReal p) volume := by
  have h := eLpNorm_le_of_euclidean_cube_oscillation f (fun x => 2 * G x) hfn
    (fun x => mul_nonneg (by norm_num) (hGn x)) hfc hf (hG.const_mul 2)
    hp hγ hsmall ?_
  · have he : eLpNorm (fun x => 2 * G x) (ENNReal.ofReal p) volume =
        2 * eLpNorm G (ENNReal.ofReal p) volume := by
      change eLpNorm ((2 : ℝ) • G) (ENNReal.ofReal p) volume = _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [he] at h
    convert h using 1 ; ac_rfl
  · intro Q hQ x hx
    obtain ⟨c, hc⟩ := hosc Q hQ
    have hQ0 : volume (euclideanBox Q) ≠ 0 := by
      rw [volume_euclideanBox]
      exact volume_box_ne_zero Q
    have hQtop : volume (euclideanBox Q) ≠ ∞ := by
      rw [volume_euclideanBox]
      exact (Q.measure_coe_lt_top volume).ne
    have h := (setOscillation_le_twice_centered volume f (euclideanBox Q) hfn
      hf.integrableOn hQ0 hQtop c).trans (mul_le_mul_right (hc x hx) 2)
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using h

end OAI.Analysis.Fourier.SquareFunction
