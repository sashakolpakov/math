import OAI.RepresentationTheory.Weil.Local.GeneralGaussianMagnitude

/-! # Gaussian Square Classes -/

namespace OAI.RepresentationTheory.Weil.Local.GaussianSquareClasses.Construction

noncomputable section

/-! Square-class invariance obtained from the actual damped Gaussian. -/

open _root_.MeasureTheory Filter
open scoped Classical _root_.Topology

theorem regularizedGaussian_square_mul
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (ψ : AddChar k ℂ) (a : k) (b : kˣ) (ε : ℝ) :
    FunctionsMetaplectic.Construction.regularizedGaussian k ψ (a * b.val ^ 2) ε =
      ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ) • FunctionsMetaplectic.Construction.regularizedGaussian k ψ a (ε / ‖b.val‖ ^ 2) := by
  let F : k → ℂ := fun x => (Real.exp (-ε * ‖x‖ ^ 2) : ℂ) * ψ ((a * b.val ^ 2) * x ^ 2 / 2)
  have h := GeneralGaussianMagnitude.Construction.integral_div_unit (Measure.addHaar : Measure k) b F
  have heq : (∫ x, F (x / b.val) ∂(Measure.addHaar : Measure k)) =
      FunctionsMetaplectic.Construction.regularizedGaussian k ψ a (ε / ‖b.val‖ ^ 2) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (Real.exp (-ε * ‖x / b.val‖ ^ 2) : ℂ) * ψ ((a * b.val ^ 2) * (x / b.val) ^ 2 / 2) = _
      have hn : -ε * ‖x / b.val‖ ^ 2 = -(ε / ‖b.val‖ ^ 2) * ‖x‖ ^ 2 := by
        rw [norm_div, div_pow]
        ring
      have hq : (a * b.val ^ 2) * (x / b.val) ^ 2 / 2 = a * x ^ 2 / 2 := by
        field_simp
      rw [hn, hq]
  rw [heq] at h
  change FunctionsMetaplectic.Construction.regularizedGaussian k ψ a (ε / ‖b.val‖ ^ 2) =
      (FunctionsMetaplectic.Construction.localModulus k b : ℝ) • FunctionsMetaplectic.Construction.regularizedGaussian k ψ (a * b.val ^ 2) ε at h
  rw [h, smul_smul, inv_mul_cancel₀ (FunctionsMetaplectic.Construction.localModulus_pos k b).ne', one_smul]

theorem positive_division_tendsto_zero_right (r : ℝ) (hr : 0 < r) :
    Tendsto (fun x : ℝ => x / r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using ((continuous_id.div_const r).continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with x hx
    exact div_pos hx hr

theorem nonarchimedean_gaussianIntegral_square_mul
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : k) (ha : a ≠ 0) (b : kˣ) :
    FunctionsMetaplectic.Construction.gaussianIntegral k ψ (a * b.val ^ 2) =
      ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ) • FunctionsMetaplectic.Construction.gaussianIntegral k ψ a := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  have hlim := (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hNondiscrete ψ hu hc hn a ha).1.comp
    (positive_division_tendsto_zero_right (‖b.val‖ ^ 2) (sq_pos_of_pos (norm_pos_iff.mpr b.ne_zero)))
  have hscaled := hlim.const_smul ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ)
  have hresult : Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ (a * b.val ^ 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ) • FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) := by
    simpa only [Function.comp_def, ← regularizedGaussian_square_mul ψ a b] using hscaled
  exact hresult.limUnder_eq

theorem nonarchimedean_gaussianIndex_square_mul
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : k) (ha : a ≠ 0) (b : kˣ) :
    FunctionsMetaplectic.Construction.gaussianIndex k ψ (a * b.val ^ 2) = FunctionsMetaplectic.Construction.gaussianIndex k ψ a := by
  rw [FunctionsMetaplectic.Construction.gaussianIndex, nonarchimedean_gaussianIntegral_square_mul hNondiscrete ψ hu hc hn a ha b,
    Complex.real_smul, Gaussian.Construction.phase_positive_mul ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹) (inv_pos.mpr (FunctionsMetaplectic.Construction.localModulus_pos k b))]
  rfl

end

end OAI.RepresentationTheory.Weil.Local.GaussianSquareClasses.Construction
