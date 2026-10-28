import OAI.MeasureTheory.Kakeya.Scaling

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- Randomization of modulated caps works for a localized extension estimate,
with exactly the same constant. No strict inequality on the exponents is used. -/
theorem local_extension_implies_packet_square_estimate {n m : ℕ}
    (μ : Measure (Space n)) {r q C δ : ℝ}
    (hr : 0 < r) (hq : 2 ≤ q) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hbound : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal r) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      MemLp (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal q) μ ∧
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal r) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    (v x : Fin m → Space n) (c : Fin m → ℂ)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) :
    Integrable (fun y ↦ (∑ i, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension
      (fun ω ↦ c i * capPacket δ (v i) (x i) ω) y‖ ^ 2) ^ (q / 2)) μ ∧
    (∫ y, (∑ i, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension
      (fun ω ↦ c i * capPacket δ (v i) (x i) ω) y‖ ^ 2) ^ (q / 2) ∂μ) ≤
      C ^ q * (∑ i, ‖c i‖ ^ r * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ^ (q / r) := by
  let g : Fin m → Space n → ℂ := fun i ω ↦ c i * capPacket δ (v i) (x i) ω
  let z : Fin m → Space n → ℂ := fun i y ↦ OAI.Analysis.Fourier.Restriction.sphericalExtension (g i) y
  let f : (Fin m → Bool) → Space n → ℂ := fun ε ω ↦ signedSum (fun i ↦ g i ω) ε
  have hq0 : 0 < q := by linarith
  have hg (i : Fin m) : Integrable (g i) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
    (integrable_capPacket δ (v i) (x i)).const_mul (c i)
  have hf (ε : Fin m → Bool) : MemLp (f ε) (ENNReal.ofReal r) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
    memLp_signedPackets hδ v x c ε hsep hr
  have hE (ε : Fin m → Bool) : OAI.Analysis.Fourier.Restriction.sphericalExtension (f ε) =
      fun y ↦ signedSum (fun i ↦ z i y) ε := by
    funext y
    exact sphericalExtension_signedSum g hg ε y
  have hi (ε : Fin m → Bool) :
      Integrable (fun y ↦ ‖signedSum (fun i ↦ z i y) ε‖ ^ q) μ := by
    have h := (hbound (f ε) (hf ε)).1.integrable_norm_rpow
      (ENNReal.ofReal_pos.mpr hq0).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hq0.le, hE ε] using h
  have hpow (ε : Fin m → Bool) :
      (∫ y, ‖signedSum (fun i ↦ z i y) ε‖ ^ q ∂μ) ≤
        C ^ q * (∑ i, ‖c i‖ ^ r * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ^ (q / r) := by
    have h := OAI.Analysis.Fourier.Restriction.integral_norm_rpow_le_of_eLpNorm_le hr hq0 hC (hf ε)
      (hbound (f ε) (hf ε)).1 (hbound (f ε) (hf ε)).2
    rw [hE ε] at h
    change (∫ y, ‖signedSum (fun i ↦ z i y) ε‖ ^ q ∂μ) ≤
      C ^ q * (∫ ω, ‖signedSum (fun i ↦ c i * capPacket δ (v i) (x i) ω) ε‖ ^ r
        ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ^ (q / r) at h
    rw [integral_norm_signedPackets_rpow hδ v x c ε hsep hr] at h
    exact h
  have hJ := integral_sign_randomization_lower z hq
    (fun i ↦ (OAI.Analysis.Fourier.Restriction.continuous_sphericalExtension (hg i)).aestronglyMeasurable) hi
  refine ⟨hJ.1, hJ.2.trans ?_⟩
  calc
    (∑ ε : Fin m → Bool, ∫ y, ‖signedSum (fun i ↦ z i y) ε‖ ^ q ∂μ) / (2 : ℝ) ^ m ≤
      (∑ _ε : Fin m → Bool,
        C ^ q * (∑ i, ‖c i‖ ^ r * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ^ (q / r)) /
          (2 : ℝ) ^ m :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun ε _ ↦ hpow ε) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

/-- An extension estimate is only needed on a region containing the rescaled
tubes. This retains its constant, including any logarithmic dependence. -/
theorem local_extension_implies_weighted_tube_overlap {n m : ℕ}
    {Ω : Set (Space n)} (hΩ : MeasurableSet Ω) {r q C δ : ℝ}
    (hr : 0 < r) (hq : 2 ≤ q) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hbound : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal r) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      MemLp (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal q) (volume.restrict Ω) ∧
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal q) (volume.restrict Ω) ≤
        ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal r) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    (v x : Fin m → Space n) (c : Fin m → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j))
    (hregion : ∀ i y, y ∈ OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i) → (δ ^ 2)⁻¹ • y ∈ Ω) :
    Integrable (fun y ↦ packetTubeOverlap δ v x c y ^ (q / 2)) volume ∧
    (∫ y, packetTubeOverlap δ v x c y ^ (q / 2)) ≤
      (δ ^ 2) ^ n * (C ^ q *
        (∑ i, ‖c i‖ ^ r * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ^ (q / r)) := by
  obtain ⟨henergy, hestimate⟩ := local_extension_implies_packet_square_estimate
    (volume.restrict Ω) hr hq hC hδ hbound v x c hsep
  let energy : Space n → ℝ := fun y ↦
    (∑ i, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ c i * capPacket δ (v i) (x i) ω) y‖ ^ 2) ^ (q / 2)
  have hind : Integrable (Ω.indicator energy) volume :=
    (integrable_indicator_iff hΩ).mpr henergy
  have hi : Integrable (fun y ↦ Ω.indicator energy ((δ ^ 2)⁻¹ • y)) volume :=
    hind.comp_smul (inv_ne_zero (pow_ne_zero 2 hδ.ne'))
  have hdom (y : Space n) : packetTubeOverlap δ v x c y ^ (q / 2) ≤
      Ω.indicator energy ((δ ^ 2)⁻¹ • y) := by
    by_cases hy : (δ ^ 2)⁻¹ • y ∈ Ω
    · rw [Set.indicator_of_mem hy]
      exact Real.rpow_le_rpow (packetTubeOverlap_nonneg δ v x c y)
        (packetTubeOverlap_le hδ v x c hv y) (by linarith)
    · have hz : packetTubeOverlap δ v x c y = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact Set.indicator_of_notMem (fun ht ↦ hy (hregion i y ht)) _
      rw [hz, Real.zero_rpow (by linarith : q / 2 ≠ 0), Set.indicator_of_notMem hy]
  have hm : AEStronglyMeasurable (fun y ↦ packetTubeOverlap δ v x c y ^ (q / 2)) volume :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ q / 2)).comp_aestronglyMeasurable
      (measurable_packetTubeOverlap δ v x c).aestronglyMeasurable
  have ho : Integrable (fun y ↦ packetTubeOverlap δ v x c y ^ (q / 2)) volume := by
    apply hi.mono' hm
    exact Filter.Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (Real.rpow_nonneg (packetTubeOverlap_nonneg δ v x c y) _)]
      exact hdom y
  refine ⟨ho, (integral_mono ho hi hdom).trans ?_⟩
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (Ω.indicator energy) (sq_nonneg δ)]
  have hdim : Module.finrank ℝ (Space n) = n := by simp [Space]
  rw [hdim, smul_eq_mul, integral_indicator hΩ]
  exact mul_le_mul_of_nonneg_left hestimate (by positivity)

/-- The cap weights can be removed without any loss beyond the two-sided
cap-volume constants, also at the critical extension exponent. -/
theorem tubeOverlap_bound_of_local_extension {n m : ℕ}
    {Ω : Set (Space n)} (hΩ : MeasurableSet Ω) {q C L U δ : ℝ}
    (hq : 2 ≤ q) (hC : 0 ≤ C) (hL : 0 < L) (hU : 0 ≤ U) (hδ : 0 < δ)
    (hbound : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      MemLp (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal q) (volume.restrict Ω) ∧
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal q) (volume.restrict Ω) ≤
        ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    (v x : Fin m → Space n) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j))
    (hregion : ∀ i y, y ∈ OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i) → (δ ^ 2)⁻¹ • y ∈ Ω)
    (hlower : ∀ i, L ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)))
    (hupper : ∀ i, (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) ≤ U)
    (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∫ y, tubeOverlap δ v x a y ^ (q / 2)) ^ (1 / (q / 2)) ≤
      ((δ ^ 2) ^ n * C ^ q * U * (2 / L) ^ q) ^ (1 / (q / 2)) *
        (∑ i, a i ^ (q / 2)) ^ (1 / (q / 2)) := by
  have hq0 : 0 < q := by linarith
  apply tubeOverlap_bound_of_packet_bound δ v x hq0 hC hL hU hlower hupper
    (fun c ↦ ?_) a ha
  simpa only [div_self hq0.ne', Real.rpow_one] using
    local_extension_implies_weighted_tube_overlap hΩ hq0 hq hC hδ hbound v x c hv hsep hregion

/-- Unit tubes whose centers lie in the unit ball fit inside one fixed ball
after the parabolic scaling used for the cap packets. -/
theorem scaled_tube_mem_ball {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    {v x y : Space n} (hv : ‖v‖ = 1) (hx : ‖x‖ ≤ 1)
    (hy : y ∈ OAI.MeasureTheory.Kakeya.tube (2 * δ) v x) :
    (δ ^ 2)⁻¹ • y ∈ Metric.ball (0 : Space n) (4 / δ ^ 2) := by
  have hd := tube_subset_ball (2 * δ) v x hy
  rw [Metric.mem_ball, dist_eq_norm, hv] at hd
  have hnorm : ‖y‖ < 4 := by
    have ht : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
      simpa only [sub_add_cancel] using norm_add_le (y - x) x
    linarith
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sq_pos_of_pos hδ)), div_eq_mul_inv, mul_comm (4 : ℝ)]
  exact mul_lt_mul_of_pos_left hnorm (inv_pos.mpr (sq_pos_of_pos hδ))

/-- The dependence on the extension constant in the overlap norm is exactly
quadratic. In particular logarithmic losses remain logarithmic. -/
theorem critical_cap_constant {q C L U : ℝ} (hq : 0 < q)
    (hC : 0 ≤ C) (hL : 0 < L) (hU : 0 ≤ U) :
    (C ^ (2 * q) * U * (2 / L) ^ (2 * q)) ^ (1 / q) =
      (U ^ (1 / q) * (2 / L) ^ (2 : ℕ)) * C ^ (2 : ℕ) := by
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) hU,
    ← Real.rpow_mul hC, ← Real.rpow_mul (by positivity : 0 ≤ 2 / L)]
  have he : 2 * q * (1 / q) = (2 : ℝ) := by field_simp
  rw [he, Real.rpow_two, Real.rpow_two]
  ring

/-- At the critical extension exponent the scale factor is precisely the
one associated with the total volume of the tubes. -/
theorem critical_cap_scale {n : ℕ} (hn : 2 ≤ n) :
    (2 * (n : ℝ) + (n - 1 : ℕ)) / ((n : ℝ) / ((n : ℝ) - 1)) -
        2 * (n - 1 : ℕ) =
      (n - 1 : ℕ) / ((n : ℝ) / ((n : ℝ) - 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  field_simp
  ring

/-- A localized critical extension estimate yields the sharp-scale tube
overlap estimate, uniformly for centers in the unit ball. The only analytic
loss is the square of the supplied extension constant. -/
theorem local_critical_extension_tube_overlap {n : ℕ} (hn : 2 ≤ n) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m : ℕ) (δ C : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ C →
      (∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
        MemLp (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
          (volume.restrict (Metric.ball (0 : Space n) (4 / δ ^ 2))) ∧
        eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
          (volume.restrict (Metric.ball (0 : Space n) (4 / δ ^ 2))) ≤
          ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) →
      ∀ (v x : Fin m → Space n), (∀ i, ‖v i‖ = 1) → (∀ i, ‖x i‖ ≤ 1) →
        (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
        ∀ (a : Fin m → ℝ), (∀ i, 0 ≤ a i) →
      (∫ y, tubeOverlap δ v x a y ^ ((n : ℝ) / ((n : ℝ) - 1))) ^
          (1 / ((n : ℝ) / ((n : ℝ) - 1))) ≤
        B * C ^ 2 * (δ ^ (n - 1) * ∑ i, a i ^ ((n : ℝ) / ((n : ℝ) - 1))) ^
          (1 / ((n : ℝ) / ((n : ℝ) - 1))) := by
  let q : ℝ := (n : ℝ) / ((n : ℝ) - 1)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 0 < q := div_pos (by linarith) (by linarith)
  have he : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n = 2 * q := by dsimp [OAI.Analysis.Fourier.LocalSmoothing.criticalExponent, q]; ring
  have hhalf : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n / 2 = q := by rw [he]; ring
  obtain ⟨L, U, hL, hU, hcap⟩ := OAI.Analysis.Fourier.Restriction.packetCap_real_comparable (n := n) (by omega)
  refine ⟨U ^ (1 / q) * (2 / L) ^ (2 : ℕ), by positivity, ?_⟩
  intro m δ C hδ hδone hC hbound v x hv hx hsep a ha
  have h := tubeOverlap_bound_of_local_extension measurableSet_ball
    (criticalExponent_gt_two hn).le hC
    (show 0 < L * δ ^ (n - 1) by positivity)
    (show 0 ≤ U * δ ^ (n - 1) by positivity) hδ hbound v x hv hsep
    (fun i y hy ↦ scaled_tube_mem_ball hδ hδone (hv i) (hx i) hy)
    (fun i ↦ (hcap δ (v i) hδ hδone (hv i)).1)
    (fun i ↦ (hcap δ (v i) hδ hδone (hv i)).2) a ha
  rw [hhalf, he] at h
  have hdim : (δ ^ 2) ^ n = δ ^ (2 * (n : ℝ)) := by
    rw [← pow_mul]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Real.rpow_natCast δ (2 * n)).symm
  have hd : δ ^ (n - 1) = δ ^ ((n - 1 : ℕ) : ℝ) := (Real.rpow_natCast δ (n - 1)).symm
  rw [hdim, hd, cap_coefficient_scale hδ hC hL hU.le hq,
    critical_cap_constant hq hC hL hU.le] at h
  have hscale : (2 * (n : ℝ) + (n - 1 : ℕ)) / q - 2 * (n - 1 : ℕ) =
      (n - 1 : ℕ) / q := critical_cap_scale hn
  rw [hscale] at h
  calc
    _ ≤ ((U ^ (1 / q) * (2 / L) ^ (2 : ℕ)) * C ^ (2 : ℕ) * δ ^ ((n - 1 : ℕ) / q)) *
        (∑ i, a i ^ q) ^ (1 / q) := h
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (ha i) _),
        hd, ← Real.rpow_mul hδ.le]
      dsimp only [q]
      simp only [div_eq_mul_inv, one_mul]
      ring

end OAI.MeasureTheory.Kakeya
