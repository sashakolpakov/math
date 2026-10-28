import OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierCoordinates

/-! # Bilinear Fourier Pairing -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierPairing.Construction

noncomputable section

section

/-! Nondegenerate bilinear Fourier transforms preserve compact local
constancy over the nonarchimedean field. -/

open _root_.MeasureTheory

theorem bilinear_fourier_compact_locallyConstant
    {F V : Type} [NontriviallyNormedField F] [CompleteSpace F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [IsUltrametricDist F]
    [NormedAddCommGroup V] [NormedSpace F V] [FiniteDimensional F V] [LocallyCompactSpace V]
    [MeasurableSpace V] [BorelSpace V] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (e : V ≃L[F] Local.FunctionsMetaplectic.Construction.Position F d)
    (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate) (L : V ≃L[F] V)
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hn : ∃ x : F, ψ x ≠ 1)
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (f : V → ℂ) (hfl : IsLocallyConstant f) (hfs : HasCompactSupport f) :
    IsLocallyConstant (fun v => ∫ x, ψ (B (L v) x) * f x ∂μ) ∧
      HasCompactSupport (fun v => ∫ x, ψ (B (L v) x) * f x ∂μ) := by
  let B' := LinearMap.BilinForm.congr e.toLinearEquiv B
  have hB' : B'.Nondegenerate := hB.congr e.toLinearEquiv
  obtain ⟨A, hA⟩ := BilinearFourierCoordinates.Construction.exists_gaussian_fourier_shift_equiv B' hB'
  have hA' : ∀ p x, B (e.symm (A p)) (e.symm x) = -Local.FunctionsMetaplectic.Construction.dot p x := hA
  let ν : Measure (Local.FunctionsMetaplectic.Construction.Position F d) := μ.map e
  let : ν.IsAddHaarMeasure := e.toContinuousAddEquiv.isAddHaarMeasure_map μ
  let k : Local.FunctionsMetaplectic.Construction.Position F d → ℂ := fun x => f (e.symm x)
  have hkl : IsLocallyConstant k := hfl.comp_continuous e.symm.continuous
  have hks : HasCompactSupport k := hfs.comp_homeomorph e.symm.toHomeomorph
  have hTl := FourierUltra.Construction.fourierIntegral_locallyConstant ψ (LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hc) ν hks
  have hTs := FourierUltra.Construction.fourierIntegral_compactSupport_of_locallyConstant hF ψ hn ν hkl hks
  let P := (L.trans e).trans A.symm
  have heq : (fun v => ∫ x, ψ (B (L v) x) * f x ∂μ) =
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ ν k ∘ P := by
    funext v
    exact BilinearFourierCoordinates.Construction.bilinear_fourier_coordinate_formula e B A hA' L ψ μ f v
  rw [heq]
  exact ⟨hTl.comp_continuous P.continuous, hTs.comp_homeomorph P.toHomeomorph⟩

end

/-! Fubini pairing for bilinear Fourier kernels, with absolute convergence. -/

open _root_.MeasureTheory

theorem bilinear_fourier_pairing
    {F V : Type} [NormedField F] [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (B : V → V → F) (hB : Continuous (fun p : V × V => B p.1 p.2))
    (μ : Measure V) [SigmaFinite μ]
    (f k : V → ℂ) (hf : Continuous f) (hk : Continuous k)
    (hfi : Integrable f μ) (hki : Integrable k μ) :
    (∫ x, k x * (∫ y, ψ (B x y) * f y ∂μ) ∂μ) =
      ∫ y, f y * (∫ x, ψ (B x y) * k x ∂μ) ∂μ := by
  let a : V × V → ℂ := fun p => k p.1 * (ψ (B p.1 p.2) * f p.2)
  have hac : Continuous a := (hk.comp continuous_fst).mul
    ((hc.comp hB).mul (hf.comp continuous_snd))
  have hai : Integrable a (μ.prod μ) := by
    apply (hki.norm.mul_prod hfi.norm).mono hac.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      simp only [a, norm_mul, hu, one_mul, norm_norm, le_refl]
  calc
    _ = ∫ x, ∫ y, k x * (ψ (B x y) * f y) ∂μ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => (integral_const_mul _ _).symm
    _ = ∫ y, ∫ x, k x * (ψ (B x y) * f y) ∂μ ∂μ := integral_integral_swap hai
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by dsimp only; ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierPairing.Construction
