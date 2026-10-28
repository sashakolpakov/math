import OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeakGaussian
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakCayleyTestCoefficients

/-! # Real Cayley Schwartz -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleySchwartz.Construction

noncomputable section

/-! Coherent coefficients of real weak Cayley forms are Schwartz amplitudes. -/

open _root_.MeasureTheory
open scoped SchwartzMap

theorem realCayleyWeylPhase_temperate {d : ℕ}
    (D : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) :
    Function.HasTemperateGrowth (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ d) D) := by
  have h := (BilinearFourierCoordinates.Construction.finiteBilinearContinuous (StandardTransvections.Construction.standardSymplecticBilinear ℝ d)).bilinear_hasTemperateGrowth
    D.symm.toContinuousLinearEquiv.hasTemperateGrowth (ContinuousLinearMap.id ℝ (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)).hasTemperateGrowth
  exact h.mul (.const (2 : ℝ)⁻¹)

theorem exists_real_cayley_coefficient_schwartz {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
    (g : FrameTransport.Construction.StandardSymplectic ℝ d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)
    (hD : ∀ x, D x = g.val x - x) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    ∃ Φ : SchwartzMap (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) ℂ, ∀ v,
      Φ v = WeakCayleyTestCoefficients.Construction.cayleyTestCoefficient RealFourierUnitary.Construction.real_nondiscrete ψ hc hu ν D f h v := by
  let q := CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ d) D
  have hphase : Function.HasTemperateGrowth (fun x => ψ (q x)) :=
    (RealCharacter.Construction.continuous_unitary_real_character_temperate ψ hc hu).comp (realCayleyWeylPhase_temperate D)
  obtain ⟨C, hC⟩ := RealWeylCoefficients.Construction.exists_real_weyl_coefficient_schwartz ψ hc hu hn (Weak.Construction.referencePositionMeasure ℝ d) f h
  let A := SchwartzMap.smulLeftCLM ℂ (fun x => ψ (q x)) C
  let e : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃L[ℝ] Local.FunctionsMetaplectic.Construction.Position ℝ (d + d) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (d + d) => ℝ) finSumFinEquiv
  obtain ⟨B, hB⟩ := RealBilinearFourier.Construction.exists_real_bilinear_fourier_schwartz e (StandardTransvections.Construction.standardSymplecticBilinear ℝ d)
    (StandardTransvections.Construction.standardSymplecticBilinear_nondegenerate d) D.symm.toContinuousLinearEquiv ψ hc hu hn ν A
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x => ψ (q x)) B, fun v => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply hphase, hB]
  rw [WeakCayleyTestCoefficients.Construction.cayleyTestCoefficient, WeakCayleyCoefficients.Construction.weakCayleyGaussian_output_coefficient RealFourierUnitary.Construction.real_nondiscrete ψ hc hu ν g D hD]
  change ψ (q v) * _ = ψ (q v) * _
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    change ψ (StandardTransvections.Construction.standardSymplecticBilinear ℝ d (D.symm v) x) * A x = _
    rw [SchwartzMap.smulLeftCLM_apply_apply hphase, hC]
    rfl

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleySchwartz.Construction
