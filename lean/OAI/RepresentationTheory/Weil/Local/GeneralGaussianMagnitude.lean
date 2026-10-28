import OAI.RepresentationTheory.Weil.Local.GaussianNonarchimedean

/-! # General Gaussian Magnitude -/

namespace OAI.RepresentationTheory.Weil.Local.GeneralGaussianMagnitude.Construction

noncomputable section

section

/-! Scalar substitution in the reference Haar integral. -/

open _root_.MeasureTheory

theorem integral_div_unit
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (μ : Measure k) [μ.IsAddHaarMeasure] (a : kˣ) (f : k → ℂ) :
    (∫ x, f (x / a.val) ∂μ) = (FunctionsMetaplectic.Construction.localModulus k a : ℝ) • ∫ x, f x ∂μ := by
  calc
    _ = ∫ x, f x ∂(DomMulAct.mk a • μ) := by
      rw [integral_domSMul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change f (x / a.val) = f ((a⁻¹).val * x)
        simp only [Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm]
    _ = _ := by
      rw [Measure.isAddLeftInvariant_eq_smul_of_regular (DomMulAct.mk a • μ) μ,
        integral_smul_nnreal_measure, addHaarScalarFactor_smul_eq_distribHaarChar μ a]
      rfl

end

/-! The magnitude of every nonzero local Gaussian coefficient. -/

open _root_.MeasureTheory
open scoped Classical ComplexConjugate

theorem compactGaussian_modulus_norm_sq
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : kˣ) (U V : OpenAddSubgroup k) (hU : IsCompact (U : Set k)) (hVU : V ≤ U)
    (hphase : ∀ t ∈ V, ψ (a.val * t ^ 2 / 2) = 1)
    (hdual : ∀ y, y ∈ U ↔ a.val * y ∈ QuadraticFourier.Construction.scalarAnnihilator ψ V.toAddSubgroup) :
    FunctionsMetaplectic.Construction.localModulus k a * ‖∫ y in (U : Set k), ψ (a.val * y ^ 2 / 2)
      ∂(Measure.addHaar : Measure k)‖ ^ 2 = FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let G := ∫ y in (U : Set k), ψ (a.val * y ^ 2 / 2) ∂(Measure.addHaar : Measure k)
  let q := QuadraticFourier.Construction.compactQuadraticFunction ψ U a.val
  have hF : FourierTensor.Construction.scalarFourierIntegral ψ Measure.addHaar q = fun x => G * conj (q (x / a.val)) := by
    funext x
    rw [GaussianNonarchimedean.Construction.scalarFourier_compactQuadratic_full ψ a.val a.ne_zero U V hVU hphase hdual]
    congr 1
    by_cases hx : x / a.val ∈ U
    · simp only [q, QuadraticFourier.Construction.compactQuadraticFunction, Set.indicator_of_mem hx]
      rw [← GaussianNonarchimedean.Construction.unitary_character_neg ψ hu]
      congr 1
      ring
    · simp [q, QuadraticFourier.Construction.compactQuadraticFunction, hx]
  have hFF := FourierTensor.Construction.scalarFourier_square_reference hNondiscrete ψ hu hc hn
    (GaussianCompact.Construction.compactQuadratic_locallyConstant ψ hu hc U a.val) (GaussianCompact.Construction.compactQuadratic_compactSupport ψ U hU a.val) 0
  change FourierTensor.Construction.scalarFourierIntegral ψ Measure.addHaar (FourierTensor.Construction.scalarFourierIntegral ψ Measure.addHaar q) 0 =
    (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) * q (-0) at hFF
  rw [hF, FourierTensor.Construction.scalarFourierIntegral] at hFF
  simp only [zero_mul, neg_zero, ψ.map_zero_eq_one, mul_one] at hFF
  have hq0 : q 0 = 1 := by simp [q, QuadraticFourier.Construction.compactQuadraticFunction]
  have hqi : (∫ x, q x ∂(Measure.addHaar : Measure k)) = G := integral_indicator U.isOpen.measurableSet
  rw [integral_const_mul, integral_div_unit Measure.addHaar a (fun x => conj (q x)),
    integral_conj, hqi, hq0, mul_one, Complex.real_smul] at hFF
  have heq : (FunctionsMetaplectic.Construction.localModulus k a : ℂ) * (G * conj G) = (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) := by
    calc
      _ = G * ((FunctionsMetaplectic.Construction.localModulus k a : ℂ) * conj G) := by ring
      _ = _ := hFF
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul] at heq
  exact_mod_cast heq

theorem nonarchimedean_gaussianIntegral_modulus_norm_sq
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) (a : kˣ) :
    FunctionsMetaplectic.Construction.localModulus k a * ‖FunctionsMetaplectic.Construction.gaussianIntegral k ψ a.val‖ ^ 2 = FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ := by
  obtain ⟨U, V, hU, hV, hVU, hphase, hdual, hradial, _⟩ :=
    GaussianCompact.Construction.exists_compactGaussian_domain hNondiscrete ψ hu hc hn a.val a.ne_zero
  have hlim := GaussianCompact.Construction.regularizedGaussian_tendsto_compact_of_domain hNondiscrete ψ hu hc a.val
    U V hU hV hVU hphase hdual hradial
  have heq : FunctionsMetaplectic.Construction.gaussianIntegral k ψ a.val =
      ∫ y in (U : Set k), ψ (a.val * y ^ 2 / 2) ∂(Measure.addHaar : Measure k) := hlim.limUnder_eq
  rw [heq]
  exact compactGaussian_modulus_norm_sq hNondiscrete ψ hu hc hn a U V hU hVU hphase hdual

theorem nonarchimedean_gaussianIntegral_norm
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) (a : kˣ) :
    ‖FunctionsMetaplectic.Construction.gaussianIntegral k ψ a.val‖ =
      Real.sqrt (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ) / Real.sqrt (FunctionsMetaplectic.Construction.localModulus k a) := by
  have h := nonarchimedean_gaussianIntegral_modulus_norm_sq hNondiscrete ψ hu hc hn a
  have hp := FunctionsMetaplectic.Construction.localModulus_pos k a
  have hs : ‖FunctionsMetaplectic.Construction.gaussianIntegral k ψ a.val‖ ^ 2 = FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ / FunctionsMetaplectic.Construction.localModulus k a := by
    apply (eq_div_iff hp.ne').mpr
    simpa only [mul_comm] using h
  rw [← Real.sqrt_div (le_of_lt (NonarchimedeanHaar.Construction.nonarchimedean_reference_scale hNondiscrete ψ hu hc hn).1),
    ← hs, Real.sqrt_sq (norm_nonneg _)]

end

end OAI.RepresentationTheory.Weil.Local.GeneralGaussianMagnitude.Construction
