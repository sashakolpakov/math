import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyEnergy
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealLinearHaarIntegral

/-! # Real Cayley Energy Determinant -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyEnergyDeterminant.Construction

noncomputable section

/-! The real Cayley energy factor depends on its difference determinant. -/

open _root_.MeasureTheory
open scoped SchwartzMap

theorem realCayleyOperator_energy_of_fourier {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
    (g : FrameTransport.Construction.StandardSymplectic ℝ d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)
    (hD : ∀ x, D x = g.val x - x) (s : ℝ)
    (hFourier : ∀ f : SchwartzMap (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) ℂ,
      (∫ v, ‖∫ x, ψ (StandardTransvections.Construction.standardSymplecticBilinear ℝ d (D.symm v) x) * f x ∂ν‖ ^ 2 ∂ν) =
        s * ∫ x, ‖f x‖ ^ 2 ∂ν) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    Local.FunctionsMetaplectic.Construction.l2Energy ℝ d (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD f) = s * Local.FunctionsMetaplectic.Construction.l2Energy ℝ d f := by
  obtain ⟨u, hu0⟩ := LocalTest.Construction.exists_test_nonzero_of_real_coordinates (ContinuousAddEquiv.refl (Local.FunctionsMetaplectic.Construction.Position ℝ d))
  obtain ⟨r, hr, hMoyal⟩ := RealMoyalIdentity.Construction.realWeyl_moyal_positive ψ hc hu hn ν u hu0
  let M := RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD
  let q := CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ d) D
  have hphase : Function.HasTemperateGrowth (fun v => ψ (q v)) :=
    (RealCharacter.Construction.continuous_unitary_real_character_temperate ψ hc hu).comp (RealCayleySchwartz.Construction.realCayleyWeylPhase_temperate D)
  obtain ⟨C, hC⟩ := RealWeylCoefficients.Construction.exists_real_weyl_coefficient_schwartz ψ hc hu hn (Weak.Construction.referencePositionMeasure ℝ d) f u
  let A := SchwartzMap.smulLeftCLM ℂ (fun v => ψ (q v)) C
  have hAa (v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) : A v = ψ (q v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d) f.val u.val v := by
    rw [SchwartzMap.smulLeftCLM_apply_apply hphase, hC]
    rfl
  have hB (v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) : WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val (M f).val v =
      ψ (q v) * ∫ x, ψ (StandardTransvections.Construction.standardSymplecticBilinear ℝ d (D.symm v) x) * A x ∂ν := by
    rw [WeylAnalysis.Construction.weylAnalysis_eq_inner RealFourierUnitary.Construction.real_nondiscrete ψ hc hu]
    rw [RealCayleyOperator.Construction.realCayleyOperator_pairing ψ hc hu hn ν g D hD,
      WeakCayleyCoefficients.Construction.weakCayleyGaussian_output_coefficient RealFourierUnitary.Construction.real_nondiscrete ψ hc hu ν g D hD]
    change ψ (q v) * _ = ψ (q v) * _
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [hAa]
  have hCi : (∫ v, ‖WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d) f.val u.val v‖ ^ 2 ∂ν) =
      r * Local.FunctionsMetaplectic.Construction.l2Energy ℝ d f := by
    simp_rw [RealCayleyEnergy.Construction.realWeyl_coefficient_reflection ψ hc hu]
    rw [integral_neg_eq_self (fun v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d =>
      ‖WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val f.val v‖ ^ 2) ν]
    exact hMoyal f
  have hAi : (∫ v, ‖A v‖ ^ 2 ∂ν) = r * Local.FunctionsMetaplectic.Construction.l2Energy ℝ d f := by
    simp_rw [hAa, norm_mul, hu, one_mul]
    exact hCi
  have hBi : (∫ v, ‖WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val (M f).val v‖ ^ 2 ∂ν) =
      s * (r * Local.FunctionsMetaplectic.Construction.l2Energy ℝ d f) := by
    simp_rw [hB, norm_mul, hu, one_mul]
    exact (hFourier A).trans (congrArg (s * ·) hAi)
  rw [hMoyal] at hBi
  apply mul_left_cancel₀ hr.ne'
  exact hBi.trans (by ring)

theorem realCayleyOperator_energy_determinant {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure] :
    ∃ s : ℝ, 0 < s ∧ ∀ (g : FrameTransport.Construction.StandardSymplectic ℝ d)
      (D : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) (hD : ∀ x, D x = g.val x - x)
      (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d),
      Local.FunctionsMetaplectic.Construction.l2Energy ℝ d (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD f) =
        (s * |LinearMap.det D.toLinearMap|) * Local.FunctionsMetaplectic.Construction.l2Energy ℝ d f := by
  let e : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃L[ℝ] Local.FunctionsMetaplectic.Construction.Position ℝ (d + d) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (d + d) => ℝ) finSumFinEquiv
  obtain ⟨s, hs, hFourier⟩ := RealBilinearFourier.Construction.exists_real_bilinear_fourier_energy_constant e (StandardTransvections.Construction.standardSymplecticBilinear ℝ d)
    (StandardTransvections.Construction.standardSymplecticBilinear_nondegenerate d) (ContinuousLinearEquiv.refl ℝ _) ψ hc hu hn ν
  refine ⟨s, hs, fun g D hD f => ?_⟩
  apply realCayleyOperator_energy_of_fourier ψ hc hu hn ν g D hD (s * |LinearMap.det D.toLinearMap|) _ f
  intro A
  have hh := RealLinearHaarIntegral.Construction.realHaar_integral_comp_symm ν D.toContinuousLinearEquiv
    (fun v => ‖∫ x, ψ (StandardTransvections.Construction.standardSymplecticBilinear ℝ d v x) * A x ∂ν‖ ^ 2)
  change (∫ v, ‖∫ x, ψ (StandardTransvections.Construction.standardSymplecticBilinear ℝ d (D.symm v) x) * A x ∂ν‖ ^ 2 ∂ν) =
    |LinearMap.det D.toLinearMap| * ∫ v, ‖∫ x, ψ (StandardTransvections.Construction.standardSymplecticBilinear ℝ d v x) * A x ∂ν‖ ^ 2 ∂ν at hh
  have hb : (∫ v, ‖∫ x, ψ (StandardTransvections.Construction.standardSymplecticBilinear ℝ d v x) * A x ∂ν‖ ^ 2 ∂ν) =
      s * ∫ x, ‖A x‖ ^ 2 ∂ν := hFourier A
  rw [hh, hb]
  ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyEnergyDeterminant.Construction
