import OAI.RepresentationTheory.Weil.Local.ComplexPowerGaussian
import OAI.RepresentationTheory.Weil.Local.ComplexTransportedNorm
import OAI.RepresentationTheory.Weil.Local.FieldCoordinates
import OAI.RepresentationTheory.Weil.Local.ArchimedeanKernel

/-! # Complex Field Gaussian -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexFieldGaussian.Construction

noncomputable section

/-! Actual Gaussian normalization in every complex topological field presentation. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k]

theorem regularizedGaussian_complexField_power
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (p : ℝ) (hNorm : ∀ z : ℂ, ‖e.symm z‖ = ‖z‖ ^ p) (a : k) (ε : ℝ) :
    FunctionsMetaplectic.Construction.regularizedGaussian k ψ a ε = (FieldCoordinates.Construction.fieldReferenceHaarFactor e he he' : ℂ) *
      ComplexPowerGaussian.Construction.complexRegularizedPowerGaussian p (FieldFourier.Construction.fieldCharacter e ψ) (e a) ε := by
  rw [FunctionsMetaplectic.Construction.regularizedGaussian, FieldCoordinates.Construction.fieldReferenceHaar_integral e he he']
  change (FieldCoordinates.Construction.fieldReferenceHaarFactor e he he' : ℂ) *
    (∫ z, (Real.exp (-ε * ‖e.symm z‖ ^ 2) : ℂ) * ψ (a * e.symm z ^ 2 / 2) ∂Measure.addHaar) = _
  congr 1
  unfold ComplexPowerGaussian.Construction.complexRegularizedPowerGaussian
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    have hn : (‖z‖ ^ p) ^ (2 : ℕ) = ‖z‖ ^ (2 * p) := by
      rw [mul_comm (2 : ℝ) p, Real.rpow_mul (norm_nonneg z), Real.rpow_two]
    rw [hNorm z, hn]
    congr 1
    change ψ (a * e.symm z ^ 2 / 2) = ψ (e.symm (e a * z ^ 2 / 2))
    congr 1
    rw [map_div₀, map_mul, map_pow, map_ofNat, RingEquiv.symm_apply_apply]

theorem complexField_gaussian_limit_positive [CompleteSpace k] [CharZero k]
    (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1)
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (a : k) (ha : a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (r : ℂ)) := by
  obtain ⟨p, hp, hp1, hNorm⟩ := ComplexTransportedNorm.Construction.continuous_complex_embedding_norm_power hArch e.symm.toRingHom he'
  obtain ⟨r, hr, ht⟩ := ComplexPowerGaussian.Construction.complex_power_gaussian_limit_positive p hp hp1 (FieldFourier.Construction.fieldCharacter e ψ)
    (ArchimedeanKernel.Construction.fieldCharacter_continuous e he' ψ hc) (ArchimedeanKernel.Construction.fieldCharacter_unitary e ψ hu)
    (ArchimedeanKernel.Construction.fieldCharacter_nontrivial e ψ hn) (e a) ((map_ne_zero e).mpr ha)
  refine ⟨(FieldCoordinates.Construction.fieldReferenceHaarFactor e he he' : ℝ) * r,
    mul_pos (FieldCoordinates.Construction.fieldReferenceHaarFactor_pos e he he') hr, ?_⟩
  have h := ht.const_mul (FieldCoordinates.Construction.fieldReferenceHaarFactor e he he' : ℂ)
  rw [Complex.ofReal_mul]
  exact h.congr fun ε => (regularizedGaussian_complexField_power e he he' ψ p hNorm a ε).symm

theorem complexField_gaussian_normalization [CompleteSpace k] [CharZero k]
    (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1)
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (a : k) (ha : a ≠ 0) :
    Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) ∧
      FunctionsMetaplectic.Construction.gaussianIntegral k ψ a ≠ 0 ∧ FunctionsMetaplectic.Construction.gaussianIndex k ψ a = 1 := by
  obtain ⟨r, hr, ht⟩ := complexField_gaussian_limit_positive hArch e he he' ψ hc hu hn a ha
  have hI : FunctionsMetaplectic.Construction.gaussianIntegral k ψ a = (r : ℂ) := ht.limUnder_eq
  refine ⟨by rwa [hI], ?_, ?_⟩
  · rw [hI]
    exact Complex.ofReal_ne_zero.mpr hr.ne'
  · rw [FunctionsMetaplectic.Construction.gaussianIndex, hI]
    exact Gaussian.Construction.phase_positive_real r hr

end

end OAI.RepresentationTheory.Weil.Local.ComplexFieldGaussian.Construction
