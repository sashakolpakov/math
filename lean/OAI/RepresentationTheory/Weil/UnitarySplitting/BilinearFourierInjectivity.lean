import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierUltra

/-! # Bilinear Fourier Injectivity -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierInjectivity.Construction

noncomputable section

/-! Fourier injectivity for any nondegenerate bilinear pairing, obtained
by identifying it with the coordinate dot pairing. -/

open _root_.MeasureTheory _root_.Topology Filter

theorem exists_bilinear_fourier_integral_ne_zero
    {F V : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [NormedAddCommGroup V] [Module F V] [FiniteDimensional F V]
    [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V]
    {d : ℕ} (e : V ≃L[F] Local.FunctionsMetaplectic.Construction.Position F d)
    (β : LinearMap.BilinForm F V) (hβ : β.Nondegenerate)
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (hn : ∃ x : F, ψ x ≠ 1) (μ : Measure V) [μ.IsAddHaarMeasure]
    (f : V → ℂ) (hfi : Integrable f μ) (hfc : Continuous f) (hf : ∃ x, f x ≠ 0) :
    ∃ v : V, (∫ x, ψ (β x v) * f x ∂μ) ≠ 0 := by
  let ν : Measure (Local.FunctionsMetaplectic.Construction.Position F d) := μ.map e
  let : ν.IsAddHaarMeasure := e.toContinuousAddEquiv.isAddHaarMeasure_map μ
  let k : Local.FunctionsMetaplectic.Construction.Position F d → ℂ := fun x => f (e.symm x)
  have hkc : Continuous k := hfc.comp e.symm.continuous
  have hki : Integrable k ν := by
    rw [show ν = μ.map e.toHomeomorph from rfl, e.toHomeomorph.measurableEmbedding.integrable_map_iff]
    change Integrable (fun x => f (e.symm (e x))) μ
    simpa only [e.symm_apply_apply] using hfi
  by_contra! hzero
  have hmod (p : Local.FunctionsMetaplectic.Construction.Position F d) : ∫ x, UltraMultiplier.Construction.modulationCharacter ψ p x * k x ∂ν = 0 := by
    let ℓ : Module.Dual F V := (dotProductBilin F F p).comp e.toLinearMap
    let v := (β.flip.toDual hβ.flip).symm ℓ
    have hv (x : V) : β x v = Local.FunctionsMetaplectic.Construction.dot p (e x) := by
      exact LinearMap.BilinForm.apply_toDual_symm_apply (B := β.flip) (hB := hβ.flip) ℓ x
    change (∫ x, UltraMultiplier.Construction.modulationCharacter ψ p x * k x ∂μ.map e.toHomeomorph) = 0
    rw [e.toHomeomorph.isClosedEmbedding.integral_map]
    have heq : (fun x : V => UltraMultiplier.Construction.modulationCharacter ψ p (e x) * k (e x)) =
        fun x => ψ (β x v) * f x := by
      funext x
      rw [hv]
      simp only [UltraMultiplier.Construction.modulationCharacter, k, e.symm_apply_apply]
    change (∫ x, UltraMultiplier.Construction.modulationCharacter ψ p (e x) * k (e x) ∂μ) = 0
    rw [heq]
    exact hzero v
  have hae := FourierUltra.Construction.complex_eq_zero_of_modulation_integrals ψ hc hu ν hn hki hkc hmod
  have heq : k = 0 := Measure.eq_of_ae_eq hae hkc continuous_const
  obtain ⟨x, hx⟩ := hf
  apply hx
  have hh := congrFun heq (e x)
  simpa only [k, e.symm_apply_apply, Pi.zero_apply] using hh

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierInjectivity.Construction
