import OAI.Analysis.PDE.Concentration.Kernel
import OAI.Analysis.Calculus.Quaternion.CompactSmooth

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory Real FourierTransform
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Fourier transform only in the real radius variable. -/
noncomputable def partialRadiusFourier (A : ℝ × E → ℂ) (η : ℝ) (ξ : E) : ℂ :=
  𝓕 (fun r : ℝ => A (r, ξ)) η

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasCompactSupport_radius_slice {A : ℝ × E → ℂ}
    (hc : HasCompactSupport A) (ξ : E) : HasCompactSupport (fun r : ℝ => A (r, ξ)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_fst)
  intro r hr
  exact ⟨(r, ξ), subset_tsupport A hr, rfl⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasCompactSupport_space_slice {A : ℝ × E → ℂ}
    (hc : HasCompactSupport A) (r : ℝ) : HasCompactSupport (fun ξ : E => A (r, ξ)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd)
  intro ξ hξ
  exact ⟨(r, ξ), subset_tsupport A hξ, rfl⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem partialRadiusFourier_reconstruction {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (s : ℝ) (ξ : E) :
    A (s, ξ) = ∫ η : ℝ,
      Complex.exp ((2 * Real.pi * s * η : ℝ) * Complex.I) * partialRadiusFourier A η ξ := by
  let f : SchwartzMap ℝ ℂ := (hasCompactSupport_radius_slice hc ξ).toSchwartzMap
    (ha.comp (contDiff_id.prodMk contDiff_const))
  have hfInv : (𝓕⁻ (𝓕 f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) = f :=
    fourierInv_fourier_eq f
  have h := congrArg (fun g : SchwartzMap ℝ ℂ => g s) hfInv
  have he : (fun η => partialRadiusFourier A η ξ) = (𝓕 f : SchwartzMap ℝ ℂ) := by
    ext η
    exact (congrFun (SchwartzMap.fourier_coe f) η).symm
  change (𝓕⁻ (𝓕 f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) s = A (s, ξ) at h
  rw [SchwartzMap.fourierInv_coe, ← he] at h
  simpa [Real.fourierInv_eq', real_inner_comm,
    RCLike.inner_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h.symm

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem partialRadiusFourier_support {A : ℝ × E → ℂ} {S : Set E}
    (hS : IsClosed S) (hs : tsupport A ⊆ Set.univ ×ˢ S) (η : ℝ) :
    tsupport (partialRadiusFourier A η) ⊆ S := by
  apply closure_minimal _ hS
  intro ξ hξ
  by_contra hn
  apply hξ
  have hz : (fun r : ℝ => A (r, ξ)) = 0 := by
    funext r
    by_contra hr
    exact hn (hs (subset_tsupport A hr)).2
  simp [partialRadiusFourier, hz, Real.fourier_eq]

/-- Fubini identifies the spatial inverse transform of the radius transform
with a single ordinary Fourier transform on the Hilbert product space. -/
theorem partialRadiusFourier_inverse_eq_joint {A : ℝ × E → ℂ}
    (ha : Continuous A) (hc : HasCompactSupport A) (η : ℝ) (x : E) :
    𝓕⁻ (partialRadiusFourier A η) x =
      𝓕 (fun z : WithLp 2 (ℝ × E) => A (WithLp.ofLp z)) (WithLp.toLp 2 (η, -x)) := by
  let F : ℝ × E → ℂ := fun p =>
    Complex.exp ((-2 * Real.pi * p.1 * η : ℝ) * Complex.I) *
      (Complex.exp ((2 * Real.pi * inner ℝ p.2 x : ℝ) * Complex.I) * A p)
  have hFc : Continuous F := by dsimp [F]; fun_prop
  have hFs : HasCompactSupport F := hc.mul_left.mul_left
  have hFi : Integrable F := hFc.integrable_of_hasCompactSupport hFs
  have hjoint :
      𝓕 (fun z : WithLp 2 (ℝ × E) => A (WithLp.ofLp z)) (WithLp.toLp 2 (η, -x)) =
        ∫ p : ℝ × E, F p := by
    rw [Real.fourier_eq']
    have he (z : WithLp 2 (ℝ × E)) :
        Complex.exp ((-2 * Real.pi * inner ℝ z (WithLp.toLp 2 (η, -x)) : ℝ) * Complex.I) •
            A (WithLp.ofLp z) = F (WithLp.ofLp z) := by
      simp only [WithLp.prod_inner_apply, inner_neg_right,
        RCLike.inner_apply, conj_trivial, smul_eq_mul, F]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    simp_rw [he]
    exact (WithLp.volume_preserving_ofLp ℝ E).integral_comp
      (MeasurableEquiv.toLp 2 (ℝ × E)).symm.measurableEmbedding F
  rw [hjoint, Measure.volume_eq_prod, integral_prod_symm _ hFi]
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [partialRadiusFourier, Real.fourier_eq']
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [RCLike.inner_apply, conj_trivial, F]
  ring_nf

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem schwartz_hilbert_product_decay (K : SchwartzMap (WithLp 2 (ℝ × E)) ℂ)
    (a b : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, ∀ x : E,
    ‖K (WithLp.toLp 2 (η, x))‖ ≤
      C * (1 + |η|) ^ (-(a : ℝ)) * (1 + ‖x‖) ^ (-(b : ℝ)) := by
  let C := 2 ^ (a + b) * (Finset.Iic (a + b, 0)).sup
    (fun i => SchwartzMap.seminorm ℝ i.1 i.2) K
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro η x
  let z := WithLp.toLp 2 (η, x)
  have ha : |η| ≤ ‖z‖ := by simpa [z, Real.norm_eq_abs] using WithLp.norm_fst_le ℝ z
  have hb : ‖x‖ ≤ ‖z‖ := by simpa [z] using WithLp.norm_snd_le ℝ z
  have hweight : (1 + |η|) ^ a * (1 + ‖x‖) ^ b ≤ (1 + ‖z‖) ^ (a + b) := by
    rw [pow_add]
    exact mul_le_mul
      (pow_le_pow_left₀ (by positivity) (by linarith) a)
      (pow_le_pow_left₀ (by positivity) (by linarith) b) (by positivity) (by positivity)
  have hbnd : ‖K z‖ * ((1 + |η|) ^ a * (1 + ‖x‖) ^ b) ≤ C := by
    calc
      _ ≤ ‖K z‖ * (1 + ‖z‖) ^ (a + b) :=
        mul_le_mul_of_nonneg_left hweight (norm_nonneg _)
      _ ≤ C := by
        simpa only [C, norm_iteratedFDeriv_zero, mul_comm] using
          SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (a + b, 0))
            le_rfl le_rfl K z
  have hdiv := (le_div_iff₀ (by positivity : 0 < (1 + |η|) ^ a * (1 + ‖x‖) ^ b)).2 hbnd
  simpa [Real.rpow_neg (by positivity : 0 ≤ 1 + |η|),
    Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖), Real.rpow_natCast,
    div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm, z] using hdiv

theorem partialRadiusFourier_inverse_decay {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, ∀ x : E,
    ‖𝓕⁻ (partialRadiusFourier A η) x‖ ≤
      C * (1 + |η|) ^ (-(a : ℝ)) * (1 + ‖x‖) ^ (-(b : ℝ)) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E
  let f : SchwartzMap (WithLp 2 (ℝ × E)) ℂ :=
    (hc.comp_homeomorph e.toHomeomorph).toSchwartzMap (ha.comp e.contDiff)
  let K : SchwartzMap (WithLp 2 (ℝ × E)) ℂ := 𝓕 f
  obtain ⟨C, hC, hbnd⟩ := schwartz_hilbert_product_decay K a b
  refine ⟨C, hC, ?_⟩
  intro η x
  rw [partialRadiusFourier_inverse_eq_joint ha.continuous hc]
  have he : (K : WithLp 2 (ℝ × E) → ℂ) =
      𝓕 (fun z : WithLp 2 (ℝ × E) => A (WithLp.ofLp z)) :=
    SchwartzMap.fourier_coe f
  rw [← he]
  simpa only [norm_neg] using hbnd η (-x)

theorem partialRadiusFourier_inverse_L1 {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ,
      Integrable (𝓕⁻ (partialRadiusFourier A η)) ∧
      (∫ x, ‖𝓕⁻ (partialRadiusFourier A η) x‖) ≤ C * (1 + |η|) ^ (-2 : ℝ) := by
  let w : E → ℝ := fun x => (1 + ‖x‖) ^ (-(Module.finrank ℝ E + 1 : ℝ))
  have hwi : Integrable w := integrable_one_add_norm (by linarith)
  obtain ⟨C, hC, hbnd⟩ := partialRadiusFourier_inverse_decay ha hc 2 (Module.finrank ℝ E + 1)
  refine ⟨C * ∫ x, w x, mul_nonneg hC (integral_nonneg fun x => by positivity), ?_⟩
  intro η
  have hbnd' (x : E) : ‖𝓕⁻ (partialRadiusFourier A η) x‖ ≤
      (C * (1 + |η|) ^ (-2 : ℝ)) * w x := by simpa [w] using hbnd η x
  have hm : AEStronglyMeasurable (𝓕⁻ (partialRadiusFourier A η)) := by
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E
    have hf : Integrable (fun z : WithLp 2 (ℝ × E) => A (WithLp.ofLp z)) :=
      (ha.comp e.contDiff).continuous.integrable_of_hasCompactSupport (hc.comp_homeomorph e.toHomeomorph)
    have he := funext (partialRadiusFourier_inverse_eq_joint ha.continuous hc η)
    rw [he]
    exact ((VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf).comp (by fun_prop)).aestronglyMeasurable
  have hi : Integrable (𝓕⁻ (partialRadiusFourier A η)) :=
    (hwi.const_mul _).mono' hm (Filter.Eventually.of_forall hbnd')
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, (C * (1 + |η|) ^ (-2 : ℝ)) * w x :=
      integral_mono hi.norm (hwi.const_mul _) hbnd'
    _ = _ := by rw [integral_const_mul]; ring

end OAI.Analysis.Fourier.WavePackets
