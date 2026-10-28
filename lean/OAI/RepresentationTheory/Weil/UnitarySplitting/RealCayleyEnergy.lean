import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyOperator
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealMoyalIdentity
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealBilinearFourier

/-! # Real Cayley Energy -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyEnergy.Construction

noncomputable section

/-! A real Cayley operator scales L² energy by one positive constant. -/

open _root_.MeasureTheory
open scoped SchwartzMap

theorem realWeyl_coefficient_reflection {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) :
    WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d) f.val u.val v =
      WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val f.val (-v) := by
  rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner RealFourierUnitary.Construction.real_nondiscrete ψ hc hu,
    WeylAnalysis.Construction.weylAnalysis_eq_inner RealFourierUnitary.Construction.real_nondiscrete ψ hc hu]
  exact Weyl.Construction.heisenbergOperator_adjoint RealFourierUnitary.Construction.real_nondiscrete ψ hc hu v f u

theorem realCayleyOperator_energy_factor {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
    (g : FrameTransport.Construction.StandardSymplectic ℝ d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)
    (hD : ∀ x, D x = g.val x - x) :
    ∃ s : ℝ, 0 < s ∧ ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d,
      Local.FunctionsMetaplectic.Construction.l2Energy ℝ d (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD f) = s * Local.FunctionsMetaplectic.Construction.l2Energy ℝ d f := by
  let e : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃L[ℝ] Local.FunctionsMetaplectic.Construction.Position ℝ (d + d) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (d + d) => ℝ) finSumFinEquiv
  obtain ⟨s, hs, hFourier⟩ := RealBilinearFourier.Construction.exists_real_bilinear_fourier_energy_constant e (StandardTransvections.Construction.standardSymplecticBilinear ℝ d)
    (StandardTransvections.Construction.standardSymplecticBilinear_nondegenerate d) D.symm.toContinuousLinearEquiv ψ hc hu hn ν
  obtain ⟨u, hu0⟩ := LocalTest.Construction.exists_test_nonzero_of_real_coordinates (ContinuousAddEquiv.refl (Local.FunctionsMetaplectic.Construction.Position ℝ d))
  obtain ⟨r, hr, hMoyal⟩ := RealMoyalIdentity.Construction.realWeyl_moyal_positive ψ hc hu hn ν u hu0
  refine ⟨s, hs, fun f => ?_⟩
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
    simp_rw [realWeyl_coefficient_reflection ψ hc hu]
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

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyEnergy.Construction
