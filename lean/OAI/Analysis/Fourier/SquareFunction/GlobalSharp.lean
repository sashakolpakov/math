import OAI.Analysis.Fourier.SquareFunction.ExpandingCubes

/-! The global sharp-function moment estimate, with the root term removed. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set BoxIntegral Filter
open scoped ENNReal Topology

/-- Pointwise control of the actual mean oscillation on every cube controls
the global positive `p` moment. The first-moment hypothesis is used only to
remove the expanding-root error, not as a substitute for the conclusion. -/
theorem global_oscillation_moment_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (f G : (ι → ℝ) → ℝ) (hfn : ∀ x, 0 ≤ f x) (hGn : ∀ x, 0 ≤ G x)
    (hfc : Continuous f) (hf : Integrable f)
    {p γ : ℝ} (hp : 1 < p) (hγ : 0 < γ)
    (hsmall : γ * ((2 : ℝ) ^ Fintype.card ι + 1) ^ p < 1)
    (hosc : ∀ Q : Box ι, IsCubeBox Q → ∀ x ∈ Q,
      setOscillation volume f Q ≤ ENNReal.ofReal (G x)) :
    (∫⁻ x, ENNReal.ofReal (f x) ^ p) ≤
      ENNReal.ofReal (1 / (1 - γ * ((2 : ℝ) ^ Fintype.card ι + 1) ^ p)) *
        (ENNReal.ofReal (((2 : ℝ) ^ Fintype.card ι + 1) / γ) ^ p *
          ∫⁻ x, ENNReal.ofReal (G x) ^ p) := by
  let A : ℝ := (2 : ℝ) ^ Fintype.card ι + 1
  let C : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - γ * A ^ p))
  let B : ℝ≥0∞ := ENNReal.ofReal (A / γ) ^ p
  let F : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (f x)
  let V : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (G x) ^ p
  let E : ℝ≥0∞ := ENNReal.ofReal A ^ p * F ^ p
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hF : F ≠ ∞ := by
    have hi := hf.hasFiniteIntegral
    change (∫⁻ x, ‖f x‖ₑ) < ∞ at hi
    simpa only [Real.enorm_eq_ofReal (hfn _)] using hi.ne
  have hE : E ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
    (ENNReal.rpow_ne_top_of_nonneg hp0.le hF)
  have hlocal (I : Box ι) (hI : IsCubeBox I) :
      (∫⁻ x in (I : Set (ι → ℝ)), ENNReal.ofReal (f x) ^ p) ≤
        C * (B * V + E * volume (I : Set (ι → ℝ)) ^ (1 - p)) := by
    let μ := volume.restrict (I : Set (ι → ℝ))
    have hoscl : ∀ N Q, Q ∈ dyadicFamily I N → ∀ x ∈ Q,
        setOscillation μ f Q ≤ ENNReal.ofReal (G x) := by
      intro N Q hQ x hx
      obtain ⟨l, -, rfl⟩ := exists_word_of_mem_dyadicFamily I hQ
      exact (setOscillation_restrict_of_subset volume f (dyadicBox I l).measurableSet_coe
        (dyadicBox_le I l)).trans_le (hosc (dyadicBox I l) (hI.dyadicBox l) x hx)
    have hi := local_oscillation_moment_bound I f G hfn hGn hfc hf.integrableOn
      hp0 hγ hsmall hoscl
    have hsplit := lintegral_max_scaled μ G hGn hA
      (ENNReal.toReal_nonneg : 0 ≤ (positiveSetMean μ f I).toReal) hγ hp0.le
    have hmean : positiveSetMean volume f I ≠ ∞ :=
      positiveSetMean_ne_top volume f I hfn hf.integrableOn (volume_box_ne_zero I)
    have hr : positiveSetMean μ f I = positiveSetMean volume f I :=
      positiveSetMean_restrict_of_subset volume f I.measurableSet_coe le_rfl
    have hμ : μ univ = volume (I : Set (ι → ℝ)) := by simp [μ]
    conv at hsplit => rhs; rw [hr, ENNReal.ofReal_toReal hmean, hμ]
    refine hi.trans ((mul_le_mul_right hsplit C).trans ?_)
    apply mul_le_mul_right
    apply add_le_add
    · exact mul_le_mul_right (setLIntegral_le_lintegral (I : Set (ι → ℝ)) _) B
    · change (ENNReal.ofReal A ^ p * positiveSetMean volume f I ^ p) * volume (I : Set (ι → ℝ)) ≤
        (ENNReal.ofReal A ^ p * F ^ p) * volume (I : Set (ι → ℝ)) ^ (1 - p)
      simpa only [mul_assoc] using mul_le_mul_right
        (positiveSetMean_root_error volume f I (volume_box_ne_zero I)
          (I.measure_coe_lt_top volume).ne hp0.le) (ENNReal.ofReal A ^ p)
  have hsup : (⨆ N, ∫⁻ x in (expandingCube ι N : Set (ι → ℝ)), ENNReal.ofReal (f x) ^ p) =
      ∫⁻ x, ENNReal.ofReal (f x) ^ p := by
    rw [← setLIntegral_iUnion_of_directed _ (expandingCube_mono ι).directed_le,
      iUnion_expandingCube, Measure.restrict_univ]
  have hlimLeft : Tendsto
      (fun N => ∫⁻ x in (expandingCube ι N : Set (ι → ℝ)), ENNReal.ofReal (f x) ^ p)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ^ p)) := by
    rw [← hsup]
    apply tendsto_atTop_iSup
    intro N M hNM
    exact lintegral_mono' (Measure.restrict_mono_set volume ((expandingCube_mono ι) hNM)) le_rfl
  have hlimError : Tendsto
      (fun N => E * volume (expandingCube ι N : Set (ι → ℝ)) ^ (1 - p)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (tendsto_volume_expandingCube_rpow ι hp) (Or.inr hE)
  have hlimRight : Tendsto
      (fun N => C * (B * V + E * volume (expandingCube ι N : Set (ι → ℝ)) ^ (1 - p)))
      atTop (𝓝 (C * (B * V))) := by
    simpa only [add_zero] using ENNReal.Tendsto.const_mul
      (tendsto_const_nhds.add hlimError) (Or.inr ENNReal.ofReal_ne_top)
  exact le_of_tendsto_of_tendsto' hlimLeft hlimRight
    (fun N => hlocal (expandingCube ι N) (expandingCube_isCube ι N))

end OAI.Analysis.Fourier.SquareFunction
