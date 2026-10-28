import OAI.Analysis.Fourier.BochnerRiesz.Kernel

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set FourierTransform Real
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_norm_le_compact_bound {F : Type*} [NormedAddCommGroup F]
    {S : Set E} (hS : IsCompact S) {f : E → F} (hf : Function.support f ⊆ S)
    {C : ℝ} (hC : ∀ x ∈ S, ‖f x‖ ≤ C) :
    (∫ x, ‖f x‖) ≤ C * volume.real S := by
  have heq : (∫ x, ‖f x‖) = ∫ x in S, ‖f x‖ := by
    rw [← integral_indicator hS.measurableSet]
    congr 1
    ext x
    by_cases hx : x ∈ S
    · simp [hx]
    · have hz : f x = 0 := by
        by_contra hn
        exact hx (hf hn)
      simp [hx, hz]
  rw [heq]
  have hb := norm_setIntegral_le_of_norm_le_const_ae' (μ := volume) (s := S)
    (f := fun x => ‖f x‖) (C := C) hS.measure_lt_top
    (Filter.Eventually.of_forall fun x hx => by simpa using hC x hx)
  exact (le_abs_self _).trans hb

/-- The fixed derivative count in the concentration argument: no derivative
above `N` enters the constant or the hypotheses. -/
theorem finite_order_fourier_decay {S : Set E} (hS : IsCompact S)
    {b : E → ℂ} {N : ℕ} (hb : ContDiff ℝ N b) (hs : tsupport b ⊆ S)
    {B : ℝ} (hB : 0 ≤ B)
    (hderiv : ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ B) (x : E) :
    ‖𝓕 b x‖ ≤
      (2 ^ N * (1 + 2 ^ N * (N + 1)) * volume.real S) * B *
        (1 + ‖x‖) ^ (-(N : ℝ)) := by
  have hsb : HasCompactSupport b := hS.of_isClosed_subset (isClosed_tsupport _) hs
  have hint (j : ℕ) (hj : j ≤ N) : Integrable (iteratedFDeriv ℝ j b) :=
    (hb.continuous_iteratedFDeriv (by exact_mod_cast hj)).integrable_of_hasCompactSupport
      (hsb.iteratedFDeriv j)
  have hInt (j : ℕ) (hj : j ≤ N) :
      (∫ y, ‖iteratedFDeriv ℝ j b y‖) ≤ B * volume.real S := by
    apply integral_norm_le_compact_bound hS
      ((support_iteratedFDeriv_subset j).trans hs)
    exact fun y _ => hderiv j hj y
  have hsmall : ‖𝓕 b x‖ ≤ B * volume.real S := by
    have h := VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ E) b x
    exact h.trans (by simpa using hInt 0 (Nat.zero_le N))
  have hdecay : ‖x‖ ^ N * ‖𝓕 b x‖ ≤
      2 ^ N * ((N + 1 : ℕ) : ℝ) * (B * volume.real S) := by
    have h := pow_mul_norm_iteratedFDeriv_fourier_le (K := (0 : ℕ∞))
      (N := (N : ℕ∞)) hb
      (fun k j hk hj => by
        have hk0 : k = 0 := by simpa using hk
        subst k
        simpa using (hint j (by exact_mod_cast hj)).norm)
      (k := 0) (n := N) (by simp) (by simp) x
    simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add,
      norm_iteratedFDeriv_zero, Finset.range_one, Finset.singleton_product,
      Finset.sum_map, Function.Embedding.sectR_apply,
      pow_zero, one_mul] at h
    change ‖x‖ ^ N * ‖𝓕 b x‖ ≤
      2 ^ N * ∑ j ∈ Finset.range (N + 1), ∫ y, ‖iteratedFDeriv ℝ j b y‖ at h
    have hbnd : (∑ j ∈ Finset.range (N + 1), ∫ y, ‖iteratedFDeriv ℝ j b y‖) ≤
        ((N + 1 : ℕ) : ℝ) * (B * volume.real S) := by
      calc
        _ ≤ ∑ j ∈ Finset.range (N + 1), B * volume.real S :=
          Finset.sum_le_sum (fun j hj => hInt j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
        _ = _ := by simp
    exact h.trans (by nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) N])
  have hlarge (hx : 0 < ‖x‖) : ‖𝓕 b x‖ ≤
      (‖x‖⁻¹) ^ N * (2 ^ N * (N + 1) * (B * volume.real S)) := by
    rw [inv_pow, ← div_eq_inv_mul]
    exact (le_div_iff₀ (pow_pos hx N)).2 (by simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hdecay)
  have h := OAI.Analysis.Fourier.BochnerRiesz.bounded_and_power_decay (norm_nonneg x) (norm_nonneg _)
    (mul_nonneg hB ENNReal.toReal_nonneg)
    (by positivity : 0 ≤ 2 ^ N * (N + 1) * (B * volume.real S)) N hsmall hlarge
  convert h using 1
  dsimp [Measure.real]
  ring

theorem finite_order_inverse_fourier_decay {S : Set E} (hS : IsCompact S)
    {b : E → ℂ} {N : ℕ} (hb : ContDiff ℝ N b) (hs : tsupport b ⊆ S)
    {B : ℝ} (hB : 0 ≤ B)
    (hderiv : ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ B) (x : E) :
    ‖𝓕⁻ b x‖ ≤
      (2 ^ N * (1 + 2 ^ N * (N + 1)) * volume.real S) * B *
        (1 + ‖x‖) ^ (-(N : ℝ)) := by
  simpa only [fourierInv_eq_fourier_neg, norm_neg] using
    finite_order_fourier_decay hS hb hs hB hderiv (-x)

/-- The scaled kernel for the cycles-normalized Fourier multiplier `b(h·)`. -/
noncomputable def scaledInverseKernel (b : E → ℂ) (h : ℝ) (x : E) : ℂ :=
  ((h ^ Module.finrank ℝ E)⁻¹ : ℝ) • 𝓕⁻ b (h⁻¹ • x)

theorem finite_order_scaled_kernel_bound {S : Set E} (hS : IsCompact S)
    {b : E → ℂ} {N : ℕ} (hb : ContDiff ℝ N b) (hs : tsupport b ⊆ S)
    {B : ℝ} (hB : 0 ≤ B)
    (hderiv : ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ B)
    {h : ℝ} (hh : 0 < h) (x : E) :
    ‖scaledInverseKernel b h x‖ ≤
      (2 ^ N * (1 + 2 ^ N * (N + 1)) * volume.real S) * B *
        (h ^ Module.finrank ℝ E)⁻¹ * (1 + ‖h⁻¹ • x‖) ^ (-(N : ℝ)) := by
  have hbnd := finite_order_inverse_fourier_decay hS hb hs hB hderiv (h⁻¹ • x)
  simpa [scaledInverseKernel, norm_smul, Real.norm_eq_abs, abs_of_pos hh,
    mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hbnd (by positivity : 0 ≤ (h ^ Module.finrank ℝ E)⁻¹)

theorem polynomial_decay_le_bracket {r : ℝ} (hr : 0 ≤ r) (m : ℕ) :
    (1 + r) ^ (-((2 * m : ℕ) : ℝ)) ≤ (1 + r ^ 2) ^ (-(m : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity),
    Real.rpow_natCast, Real.rpow_natCast]
  apply inv_le_inv₀ (by positivity) (by positivity) |>.2
  calc
    (1 + r ^ 2) ^ m ≤ ((1 + r) ^ 2) ^ m :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) m
    _ = _ := by rw [pow_mul]

/-- The Japanese-bracket majorant has precisely the fixed even derivative
order, as required to compare with the regularizing probability kernel. -/
theorem finite_order_scaled_kernel_bracket {S : Set E} (hS : IsCompact S)
    {b : E → ℂ} {m : ℕ} (hb : ContDiff ℝ (2 * m : ℕ) b) (hs : tsupport b ⊆ S)
    {B : ℝ} (hB : 0 ≤ B)
    (hderiv : ∀ j ≤ 2 * m, ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ B)
    {h : ℝ} (hh : 0 < h) (x : E) :
    ‖scaledInverseKernel b h x‖ ≤
      (2 ^ (2 * m) * (1 + 2 ^ (2 * m) * (2 * m + 1)) * volume.real S) * B *
        (h ^ Module.finrank ℝ E)⁻¹ * (1 + ‖h⁻¹ • x‖ ^ 2) ^ (-(m : ℝ)) := by
  have ht := finite_order_scaled_kernel_bound hS hb hs hB hderiv hh x
  simp only [Nat.cast_mul, Nat.cast_ofNat] at ht
  apply ht.trans
  have hp := polynomial_decay_le_bracket (norm_nonneg (h⁻¹ • x)) m
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hp
  apply mul_le_mul_of_nonneg_left hp
  positivity

end OAI.Analysis.PDE.Concentration
