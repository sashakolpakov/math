import OAI.Analysis.Fourier.SquareFunction.Dyadic.Sharp
import OAI.Analysis.Fourier.SquareFunction.Dyadic.Differentiation

/-! The finite sharp-function theorem specialized to actual dyadic boxes. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set BoxIntegral
open scoped ENNReal

/-- Actual dyadic descendants of a coordinate box satisfy the scale-uniform
sharp estimate. All analytic and parent-geometry hypotheses are discharged. -/
theorem dyadic_box_sharp_moment {ι : Type*} [Fintype ι] [Nonempty ι]
    (I : Box ι) (N : ℕ) (f : (ι → ℝ) → ℝ) (hfn : ∀ x, 0 ≤ f x)
    (hf : IntegrableOn f (I : Set (ι → ℝ)))
    {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    (hsmall : γ * ((2 : ℝ) ^ Fintype.card ι + 1) ^ p < 1) :
    let μ := volume.restrict (I : Set (ι → ℝ))
    let s := dyadicFamily I N
    (∫⁻ x, familySup s (positiveSetMean μ f) x ^ p ∂μ) ≤
      ENNReal.ofReal (1 / (1 - γ * ((2 : ℝ) ^ Fintype.card ι + 1) ^ p)) *
        ∫⁻ x, ENNReal.ofReal (max
          (((2 : ℝ) ^ Fintype.card ι + 1) * ((familySup s (setOscillation μ f) x).toReal / γ))
          (((2 : ℝ) ^ Fintype.card ι + 1) * (positiveSetMean μ f I).toReal)) ^ p ∂μ := by
  let μ := volume.restrict (I : Set (ι → ℝ))
  let s := dyadicFamily I N
  have : IsFiniteMeasure μ := ⟨by
    change volume.restrict (I : Set (ι → ℝ)) univ < ∞
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact I.measure_coe_lt_top volume⟩
  have hmeas (Q : Set (ι → ℝ)) (hQ : Q ∈ s) : MeasurableSet Q :=
    dyadicFamily_measurable I N hQ
  have hμQ (Q : Set (ι → ℝ)) (hQ : Q ∈ s) : μ Q = volume Q := by
    obtain ⟨l, -, rfl⟩ := exists_word_of_mem_dyadicFamily I hQ
    change volume.restrict (I : Set (ι → ℝ)) (dyadicBox I l : Set (ι → ℝ)) = _
    rw [Measure.restrict_apply (dyadicBox I l).measurableSet_coe]
    exact congrArg volume (inter_eq_left.mpr (dyadicBox_le I l))
  have hQ0 (Q : Set (ι → ℝ)) (hQ : Q ∈ s) : μ Q ≠ 0 := by
    rw [hμQ Q hQ]
    obtain ⟨l, -, rfl⟩ := exists_word_of_mem_dyadicFamily I hQ
    exact volume_box_ne_zero _
  have hfi : Integrable f μ := hf
  have hmean (Q : Set (ι → ℝ)) (hQ : Q ∈ s) : positiveSetMean μ f Q ≠ ∞ :=
    positiveSetMean_ne_top μ f Q hfn hfi.integrableOn (hQ0 Q hQ)
  have hosc (Q : Set (ι → ℝ)) (hQ : Q ∈ s) : setOscillation μ f Q ≠ ∞ :=
    setOscillation_ne_top μ f Q hfi.integrableOn (hQ0 Q hQ) (measure_ne_top μ Q)
  have hI : (I : Set (ι → ℝ)) ∈ s := dyadicBox_mem_dyadicFamily I [] (by simp)
  apply finite_dyadic_sharp_moment μ f hfn s (dyadicFamily_laminar I N) hmeas hQ0
    hmean hosc (I : Set (ι → ℝ)) (hmean _ hI) (by positivity) hp hγ hsmall
  intro Q hQ hroot
  obtain ⟨P, hP, hQP, hvol⟩ := dyadicFamily_parent I N hQ hroot
  refine ⟨P, hP, hQP, ?_⟩
  rw [hμQ P hP, hμQ Q hQ]
  exact hvol.le

/-- Removing the finite-depth restriction: a pointwise bound for the mean
oscillations of a continuous function controls its full local positive moment.
The root-average term is retained explicitly. -/
theorem local_oscillation_moment_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (I : Box ι) (f G : (ι → ℝ) → ℝ) (hfn : ∀ x, 0 ≤ f x) (hGn : ∀ x, 0 ≤ G x)
    (hfc : Continuous f) (hf : IntegrableOn f (I : Set (ι → ℝ)))
    {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    (hsmall : γ * ((2 : ℝ) ^ Fintype.card ι + 1) ^ p < 1)
    (hosc : ∀ N Q, Q ∈ dyadicFamily I N → ∀ x ∈ Q,
      setOscillation (volume.restrict (I : Set (ι → ℝ))) f Q ≤ ENNReal.ofReal (G x)) :
    let μ := volume.restrict (I : Set (ι → ℝ))
    (∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ) ≤
      ENNReal.ofReal (1 / (1 - γ * ((2 : ℝ) ^ Fintype.card ι + 1) ^ p)) *
        ∫⁻ x, ENNReal.ofReal (max
          (((2 : ℝ) ^ Fintype.card ι + 1) * (G x / γ))
          (((2 : ℝ) ^ Fintype.card ι + 1) * (positiveSetMean μ f I).toReal)) ^ p ∂μ := by
  let μ := volume.restrict (I : Set (ι → ℝ))
  let A : ℝ := (2 : ℝ) ^ Fintype.card ι + 1
  let C := ENNReal.ofReal (1 / (1 - γ * A ^ p))
  let M : ℕ → (ι → ℝ) → ℝ≥0∞ := fun N => familySup (dyadicFamily I N) (positiveSetMean μ f)
  let V : (ι → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal
    (max (A * (G x / γ)) (A * (positiveSetMean μ f I).toReal)) ^ p
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hμQ (N : ℕ) (Q : Set (ι → ℝ)) (hQ : Q ∈ dyadicFamily I N) : μ Q = volume Q := by
    obtain ⟨l, -, rfl⟩ := exists_word_of_mem_dyadicFamily I hQ
    change volume.restrict (I : Set (ι → ℝ)) (dyadicBox I l : Set (ι → ℝ)) = _
    rw [Measure.restrict_apply (dyadicBox I l).measurableSet_coe]
    exact congrArg volume (inter_eq_left.mpr (dyadicBox_le I l))
  have hQ0 (N : ℕ) (Q : Set (ι → ℝ)) (hQ : Q ∈ dyadicFamily I N) : μ Q ≠ 0 := by
    rw [hμQ N Q hQ]
    obtain ⟨l, -, rfl⟩ := exists_word_of_mem_dyadicFamily I hQ
    exact volume_box_ne_zero _
  have hQtop (N : ℕ) (Q : Set (ι → ℝ)) (hQ : Q ∈ dyadicFamily I N) : μ Q ≠ ∞ := by
    rw [hμQ N Q hQ]
    obtain ⟨l, -, rfl⟩ := exists_word_of_mem_dyadicFamily I hQ
    exact (dyadicBox I l).measure_coe_lt_top volume |>.ne
  have hN (N : ℕ) : (∫⁻ x, M N x ^ p ∂μ) ≤ C * ∫⁻ x, V x ∂μ := by
    have h := dyadic_box_sharp_moment I N f hfn hf hp hγ hsmall
    refine h.trans (mul_le_mul_right (lintegral_mono (fun x => ?_)) C)
    have hS : familySup (dyadicFamily I N) (setOscillation μ f) x ≤ ENNReal.ofReal (G x) := by
      apply iSup_le
      intro Q
      by_cases hx : x ∈ Q.val
      · simpa only [Set.indicator_of_mem hx] using hosc N Q.val Q.property x hx
      · simp only [Set.indicator_of_notMem hx]
        exact bot_le
    have hSr : (familySup (dyadicFamily I N) (setOscillation μ f) x).toReal ≤ G x := by
      simpa only [ENNReal.toReal_ofReal (hGn x)] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hS
    apply ENNReal.rpow_le_rpow _ hp.le
    apply ENNReal.ofReal_le_ofReal
    exact max_le_max (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hSr hγ.le) hA) le_rfl
  have hmeas (N : ℕ) : Measurable (M N) :=
    measurable_familySup _ (fun Q hQ => dyadicFamily_measurable I N hQ) _
  have hmono : Monotone M := fun N K hNK x =>
    familySup_mono (dyadicFamily_mono I hNK) _ x
  change (∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ) ≤ C * ∫⁻ x, V x ∂μ
  calc
    _ ≤ ∫⁻ x, (⨆ N, M N x) ^ p ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem I.measurableSet_coe] with x hx
      exact ENNReal.rpow_le_rpow
        (continuousAt_le_iSup_dyadic_means I μ f hx hfc.continuousAt (hfn x) hQ0 hQtop) hp.le
    _ = ∫⁻ x, ⨆ N, M N x ^ p ∂μ := by
      apply lintegral_congr
      intro x
      exact (ENNReal.orderIsoRpow p hp).map_iSup (fun N => M N x)
    _ = ⨆ N, ∫⁻ x, M N x ^ p ∂μ :=
      lintegral_iSup (fun N => (hmeas N).pow_const p)
        (fun N K hNK x => ENNReal.rpow_le_rpow (hmono hNK x) hp.le)
    _ ≤ _ := iSup_le hN

end OAI.Analysis.Fourier.SquareFunction
