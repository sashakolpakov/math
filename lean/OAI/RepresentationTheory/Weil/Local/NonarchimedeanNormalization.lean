import OAI.RepresentationTheory.Weil.Local.FourierTensor

/-! # Nonarchimedean Normalization -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanNormalization.Construction

noncomputable section

/-! Fourier inversion for the exact self-dual measure defined in LocalWeil. -/

open _root_.MeasureTheory

theorem positionMeasure_reference_scale
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (n : ℕ) (ψ : AddChar k ℂ) (hc : 0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ) :
    FunctionsMetaplectic.Construction.positionMeasure k n ψ = ENNReal.ofReal ((Real.sqrt (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ))⁻¹ ^ n) •
      Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k)) := by
  let : (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
    FourierTools.Construction.selfDualMeasure_isAddHaarMeasure_of_scale_pos k ψ hc
  unfold FunctionsMetaplectic.Construction.positionMeasure
  refine Measure.pi_eq (μ := fun _ : Fin n => FunctionsMetaplectic.Construction.selfDualMeasure k ψ) fun s _ => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [FunctionsMetaplectic.Construction.selfDualMeasure, Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (inv_nonneg.mpr (Real.sqrt_nonneg _))]

theorem fourierIntegral_reference_normalized
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (n : ℕ) (ψ : AddChar k ℂ) (hc : 0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ)
    (f : FunctionsMetaplectic.Construction.Position k n → ℂ) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f x =
      ((Real.sqrt (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ))⁻¹ ^ n : ℝ) *
        FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))) f x := by
  rw [positionMeasure_reference_scale n ψ hc, FunctionsMetaplectic.Construction.fourierIntegral, integral_smul_measure,
    ENNReal.toReal_ofReal (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _), Complex.real_smul]
  rfl

theorem nonarchimedean_fourier_inversion_selfDual
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
      (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val) x = f.val (-x) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let C : ℝ := FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ
  have hC : 0 < C := (NonarchimedeanHaar.Construction.nonarchimedean_reference_scale hNondiscrete ψ hu hc hn).1
  let a : ℝ := (Real.sqrt C)⁻¹ ^ n
  let μ : Measure (FunctionsMetaplectic.Construction.Position k n) := Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))
  have hF (g : FunctionsMetaplectic.Construction.Position k n → ℂ) :
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) g = (a : ℂ) • FunctionsMetaplectic.Construction.fourierIntegral ψ μ g :=
    funext (fourierIntegral_reference_normalized n ψ hC g)
  rw [hF, hF, FunctionsMetaplectic.Construction.fourierIntegral_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  obtain ⟨hf, hs⟩ := NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property
  have hsq := FourierTensor.Construction.nonarchimedean_fourier_square_reference hNondiscrete n ψ hu hc hn hf hs x
  change FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x = (C : ℂ) ^ n * f.val (-x) at hsq
  rw [hsq]
  have hscaleR : a ^ 2 * C ^ n = 1 := by
    calc
      _ = ((Real.sqrt C)⁻¹ ^ 2 * C) ^ n := by
        dsimp only [a]
        rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n 2]
      _ = 1 := by
        rw [inv_pow, Real.sq_sqrt hC.le, inv_mul_cancel₀ hC.ne', one_pow]
  have hscale : (a : ℂ) ^ 2 * (C : ℂ) ^ n = 1 := by exact_mod_cast hscaleR
  calc
    _ = ((a : ℂ) ^ 2 * (C : ℂ) ^ n) * f.val (-x) := by ring
    _ = _ := by rw [hscale, one_mul]

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanNormalization.Construction
