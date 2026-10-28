import OAI.Analysis.Fourier.WavePackets.PartialFourier

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory Real FourierTransform
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_joint_partialRadiusFourier {A : ℝ × E → ℂ}
    (ha : Continuous A) (hc : HasCompactSupport A) :
    Continuous (fun p : ℝ × E => partialRadiusFourier A p.1 p.2) := by
  obtain ⟨B, hB⟩ := ha.bounded_above_of_compact_support hc
  let S := Prod.fst '' tsupport A
  have hS : IsCompact S := hc.image continuous_fst
  have hb : Integrable (S.indicator (fun _ : ℝ => B)) :=
    (integrable_indicator_iff hS.measurableSet).2
      (integrableOn_const (C := B) hS.measure_lt_top.ne)
  unfold partialRadiusFourier
  simp_rw [Real.fourier_eq', smul_eq_mul]
  apply continuous_of_dominated (bound := S.indicator (fun _ : ℝ => B))
  · intro p
    apply Continuous.aestronglyMeasurable
    fun_prop
  · intro p
    apply Filter.Eventually.of_forall
    intro r
    by_cases hr : r ∈ S
    · simpa [hr, Complex.norm_exp] using hB (r, p.2)
    · have hz : A (r, p.2) = 0 := by
        by_contra hn
        exact hr ⟨(r, p.2), subset_tsupport A hn, rfl⟩
      simp [hz, hr]
  · exact hb
  · apply Filter.Eventually.of_forall
    intro r
    fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_partialRadiusFourier {A : ℝ × E → ℂ}
    (ha : Continuous A) (hc : HasCompactSupport A) (η : ℝ) :
    Continuous (partialRadiusFourier A η) :=
  (continuous_joint_partialRadiusFourier ha hc).comp (continuous_const.prodMk continuous_id)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasCompactSupport_partialRadiusFourier {A : ℝ × E → ℂ}
    (hc : HasCompactSupport A) (η : ℝ) : HasCompactSupport (partialRadiusFourier A η) := by
  have hS := hc.image continuous_snd
  apply hS.of_isClosed_subset (isClosed_tsupport _)
  exact partialRadiusFourier_support hS.isClosed (fun p hp => ⟨trivial, ⟨p, hp, rfl⟩⟩) η

/-- The separated multipliers are genuine smooth compactly supported symbols.
Smoothness follows from a Schwartz slice of the joint Fourier transform and
Fourier inversion; there is no parameterwise regularity assumption. -/
theorem contDiff_partialRadiusFourier {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (η : ℝ) :
    ContDiff ℝ ∞ (partialRadiusFourier A η) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E
  let f : SchwartzMap (WithLp 2 (ℝ × E)) ℂ :=
    (hc.comp_homeomorph e.toHomeomorph).toSchwartzMap (ha.comp e.contDiff)
  let K : SchwartzMap (WithLp 2 (ℝ × E)) ℂ := 𝓕 f
  let g : E → WithLp 2 (ℝ × E) := fun x => e.symm (η, -x)
  let L : E →L[ℝ] WithLp 2 (ℝ × E) :=
    e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ E)
  have hg : g.HasTemperateGrowth := by
    have ht : (fun x => e.symm (η, 0) - L x).HasTemperateGrowth := by fun_prop
    convert ht using 1
    funext x
    dsimp [g, L]
    rw [← map_sub]
    simp
  have hnorm (x : E) : ‖x‖ ≤ 1 * (1 + ‖g x‖) ^ 1 := by
    have h := WithLp.norm_snd_le ℝ (g x)
    change ‖-x‖ ≤ ‖g x‖ at h
    simp only [norm_neg] at h
    simpa only [one_mul, pow_one] using h.trans (show ‖g x‖ ≤ 1 + ‖g x‖ by linarith)
  let Ks : SchwartzMap E ℂ := SchwartzMap.compCLM ℝ hg ⟨1, 1, hnorm⟩ K
  have he : (Ks : E → ℂ) = 𝓕⁻ (partialRadiusFourier A η) := by
    funext x
    change K (g x) = _
    rw [partialRadiusFourier_inverse_eq_joint ha.continuous hc]
    exact congrFun (SchwartzMap.fourier_coe f) (g x)
  have hci := continuous_partialRadiusFourier ha.continuous hc η
  have hi : Integrable (partialRadiusFourier A η) :=
    hci.integrable_of_hasCompactSupport (hasCompactSupport_partialRadiusFourier hc η)
  have hinv : Integrable (𝓕⁻ (partialRadiusFourier A η)) := by rw [← he]; exact Ks.integrable
  have hfour : Integrable (𝓕 (partialRadiusFourier A η)) := by
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hinv.comp_neg
  have hid := hci.fourier_fourierInv_eq hi hfour
  rw [← he] at hid
  have hs : ((𝓕 Ks : SchwartzMap E ℂ) : E → ℂ) = partialRadiusFourier A η :=
    (SchwartzMap.fourier_coe Ks).trans hid
  rw [← hs]
  exact (𝓕 Ks : SchwartzMap E ℂ).smooth ⊤

end OAI.Analysis.Fourier.WavePackets
