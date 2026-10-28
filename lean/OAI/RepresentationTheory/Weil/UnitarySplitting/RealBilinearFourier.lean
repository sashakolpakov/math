import OAI.RepresentationTheory.Weil.UnitarySplitting.RealReconstructionHaar
import OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierCoordinates

/-! # Real Bilinear Fourier -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealBilinearFourier.Construction

noncomputable section

section

/-! Real bilinear Fourier transforms preserve Schwartz functions. -/

open _root_.MeasureTheory
open scoped SchwartzMap

theorem exists_real_fourier_schwartz {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d)) [μ.IsAddHaarMeasure] (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) :
    ∃ Φ : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ, ∀ x, Φ x = Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x := by
  obtain ⟨a, ha, rfl⟩ := RealFourier.Construction.continuous_nontrivial_real_character ψ hc hu hn
  let L := (LinearEquiv.smulOfUnit (Units.mk0 a ha) : Local.FunctionsMetaplectic.Construction.Position ℝ d ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.Position ℝ d).toContinuousLinearEquiv
  let c := Measure.addHaarScalarFactor μ (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d))
  have hμ : μ = c • volume := Measure.isAddLeftInvariant_eq_smul_of_regular μ volume
  refine ⟨(c : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L (RealFourier.Construction.coordinateSchwartzFourier d f), fun x => ?_⟩
  change (c : ℂ) * RealFourier.Construction.coordinateSchwartzFourier d f (a • x) = _
  rw [RealFourier.Construction.coordinateSchwartzFourier_apply, ← RealFourierUnitary.Construction.real_fourier_frequency a]
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  rw [hμ, integral_smul_nnreal_measure]
  rfl

theorem exists_real_bilinear_fourier_schwartz
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {d : ℕ}
    (e : V ≃L[ℝ] Local.FunctionsMetaplectic.Construction.Position ℝ d) (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (L : V ≃L[ℝ] V) (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (μ : Measure V) [μ.IsAddHaarMeasure] (f : SchwartzMap V ℂ) :
    ∃ Φ : SchwartzMap V ℂ, ∀ v, Φ v = ∫ x, ψ (B (L v) x) * f x ∂μ := by
  let B' := LinearMap.BilinForm.congr e.toLinearEquiv B
  have hB' : B'.Nondegenerate := hB.congr e.toLinearEquiv
  obtain ⟨A, hA⟩ := BilinearFourierCoordinates.Construction.exists_gaussian_fourier_shift_equiv B' hB'
  have hA' : ∀ p x, B (e.symm (A p)) (e.symm x) = -Local.FunctionsMetaplectic.Construction.dot p x := hA
  let ν : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d) := μ.map e
  let : ν.IsAddHaarMeasure := e.toContinuousAddEquiv.isAddHaarMeasure_map μ
  let k := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f
  obtain ⟨Φ, hΦ⟩ := exists_real_fourier_schwartz ψ hc hu hn ν k
  let P := (L.trans e).trans A.symm
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ P Φ, fun v => ?_⟩
  change Φ (P v) = _
  rw [hΦ]
  exact (BilinearFourierCoordinates.Construction.bilinear_fourier_coordinate_formula e B A hA' L ψ μ f v).symm

end

/-! Positive energy scaling for real nondegenerate bilinear Fourier transforms. -/

open _root_.MeasureTheory
open scoped SchwartzMap

theorem realFourier_energy {d : ℕ} (a : ℝ) (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) :
    (∫ x : Local.FunctionsMetaplectic.Construction.Position ℝ d, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral (RealFourier.Construction.realCharacter a) volume f x‖ ^ 2) =
      |a|⁻¹ ^ d * ∫ x : Local.FunctionsMetaplectic.Construction.Position ℝ d, ‖f x‖ ^ 2 := by
  simp_rw [RealFourierUnitary.Construction.real_fourier_frequency a, ← RealFourier.Construction.coordinateSchwartzFourier_apply]
  have hh := Measure.integral_comp_smul (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d))
    (fun x => ‖RealFourier.Construction.coordinateSchwartzFourier d f x‖ ^ 2) a
  rw [RealFourier.Construction.coordinateSchwartzFourier_integral_norm_sq] at hh
  simpa only [Module.finrank_pi, Fintype.card_fin, abs_inv, abs_pow, inv_pow, smul_eq_mul] using hh

theorem exists_real_bilinear_fourier_energy_constant
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {d : ℕ}
    (e : V ≃L[ℝ] Local.FunctionsMetaplectic.Construction.Position ℝ d) (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (L : V ≃L[ℝ] V) (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∃ r : ℝ, 0 < r ∧ ∀ f : SchwartzMap V ℂ,
      (∫ v, ‖∫ x, ψ (B (L v) x) * f x ∂μ‖ ^ 2 ∂μ) = r * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  obtain ⟨a, ha, rfl⟩ := RealFourier.Construction.continuous_nontrivial_real_character ψ hc hu hn
  let B' := LinearMap.BilinForm.congr e.toLinearEquiv B
  obtain ⟨A, hA⟩ := BilinearFourierCoordinates.Construction.exists_gaussian_fourier_shift_equiv B' (hB.congr e.toLinearEquiv)
  have hA' : ∀ p x, B (e.symm (A p)) (e.symm x) = -Local.FunctionsMetaplectic.Construction.dot p x := hA
  let P := (L.trans e).trans A.symm
  let η : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d) := μ.map e
  let ζ : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d) := μ.map P
  let : η.IsAddHaarMeasure := e.toContinuousAddEquiv.isAddHaarMeasure_map μ
  let : ζ.IsAddHaarMeasure := P.toContinuousAddEquiv.isAddHaarMeasure_map μ
  let c := Measure.addHaarScalarFactor η (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d))
  let b := Measure.addHaarScalarFactor ζ (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d))
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure η volume
  have hbpos : 0 < b := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ζ volume
  have hη : η = c • volume := Measure.isAddLeftInvariant_eq_smul_of_regular η volume
  have hζ : ζ = b • volume := Measure.isAddLeftInvariant_eq_smul_of_regular ζ volume
  refine ⟨(c : ℝ) * (b : ℝ) * |a|⁻¹ ^ d,
    mul_pos (mul_pos hcpos hbpos) (pow_pos (inv_pos.mpr (abs_pos.mpr ha)) d), fun f => ?_⟩
  let k := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f
  have hT (v : V) : (∫ x, RealFourier.Construction.realCharacter a (B (L v) x) * f x ∂μ) =
      (c : ℂ) * Local.FunctionsMetaplectic.Construction.fourierIntegral (RealFourier.Construction.realCharacter a) volume k (P v) := by
    rw [BilinearFourierCoordinates.Construction.bilinear_fourier_coordinate_formula e B A hA' L (RealFourier.Construction.realCharacter a) μ f v]
    change Local.FunctionsMetaplectic.Construction.fourierIntegral (RealFourier.Construction.realCharacter a) η k (P v) = _
    unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
    rw [hη, integral_smul_nnreal_measure]
    rfl
  have hinput : (∫ x, ‖f x‖ ^ 2 ∂μ) = (c : ℝ) * ∫ x : Local.FunctionsMetaplectic.Construction.Position ℝ d, ‖k x‖ ^ 2 := by
    have hm : (∫ x, ‖k x‖ ^ 2 ∂η) = ∫ x, ‖f x‖ ^ 2 ∂μ := by
      change (∫ x, ‖f (e.symm x)‖ ^ 2 ∂μ.map e.toHomeomorph) = _
      rw [e.toHomeomorph.isClosedEmbedding.integral_map]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change ‖f (e.symm (e x))‖ ^ 2 = ‖f x‖ ^ 2
        rw [e.symm_apply_apply]
    rw [← hm, hη, integral_smul_nnreal_measure]
    rfl
  have houtput : (∫ v, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral (RealFourier.Construction.realCharacter a) volume k (P v)‖ ^ 2 ∂μ) =
      (b : ℝ) * (|a|⁻¹ ^ d * ∫ x : Local.FunctionsMetaplectic.Construction.Position ℝ d, ‖k x‖ ^ 2) := by
    have hm : (∫ p, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral (RealFourier.Construction.realCharacter a) volume k p‖ ^ 2 ∂ζ) =
        ∫ v, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral (RealFourier.Construction.realCharacter a) volume k (P v)‖ ^ 2 ∂μ := by
      change (∫ p, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral (RealFourier.Construction.realCharacter a) volume k p‖ ^ 2 ∂μ.map P.toHomeomorph) = _
      rw [P.toHomeomorph.isClosedEmbedding.integral_map]
      rfl
    rw [← hm, hζ, integral_smul_nnreal_measure, realFourier_energy]
    rfl
  simp_rw [hT, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg c.coe_nonneg, mul_pow]
  rw [integral_const_mul, houtput, hinput]
  ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealBilinearFourier.Construction
