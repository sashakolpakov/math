import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.RealNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexNormalization

/-! # Archimedean Weyl Energy -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylEnergy.LocalAnalysis

noncomputable section

/-! Exact Weyl orthogonality with the prescribed self-dual phase measure
and the oscillator's reference position measure, at real and complex places. -/

open _root_.MeasureTheory
open scoped NNReal

theorem archimedeanWeyl_energy
    {k : Type} [NormedField k] [LocallyCompactSpace k] [CharZero k]
    [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)
    (μ : Measure k) [μ.IsAddHaarMeasure]
    (hStable : ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin N => μ)) f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k N)
    (hInv : ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin N => μ))
        (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin N => μ)) f.val) x = f.val (-x))
    (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val u.val v‖ ^ 2
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) = Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N u := by
  let η := Measure.pi (fun _ : Fin N => μ)
  let ν := Measure.pi (fun _ : Fin N ⊕ Fin N => μ)
  let c := Measure.addHaarScalarFactor (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) η
  have href : UnitarySplitting.Weak.Construction.referencePositionMeasure k N = c • η :=
    Measure.isAddLeftInvariant_eq_smul (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) η
  have henergy : (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ η f.val u.val v‖ ^ 2 ∂ν) =
      (∫ x, ‖f.val x‖ ^ 2 ∂η) * ∫ x, ‖u.val x‖ ^ 2 ∂η := by
    rw [← (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin N ⊕ Fin N => μ)).integral_comp
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin N => k)).symm.measurableEmbedding]
    exact WeylFourier.LocalAnalysis.weylCoefficient_product_energy η ψ hu hc hStable hInv f u
  have hC (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
      UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val u.val v =
        (c : ℂ) * UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ η f.val u.val v := by
    rw [UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient, href, integral_smul_nnreal_measure]
    rfl
  have hE (a : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) : Local.FunctionsMetaplectic.Construction.l2Energy k N a = (c : ℝ) * ∫ x, ‖a.val x‖ ^ 2 ∂η := by
    change (∫ x, ‖a.val x‖ ^ 2 ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure k N) = _
    rw [href, integral_smul_nnreal_measure]
    rfl
  simp_rw [hC, norm_mul, mul_pow]
  rw [integral_const_mul, henergy, hE, hE]
  have hcNorm : ‖(c : ℂ)‖ = (c : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg c.property
  rw [hcNorm]
  ring

theorem realWeyl_energy {N : ℕ} (ψ : AddChar ℝ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) :
    (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ N) f.val u.val v‖ ^ 2
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ)) =
      Local.FunctionsMetaplectic.Construction.l2Energy ℝ N f * Local.FunctionsMetaplectic.Construction.l2Energy ℝ N u := by
  obtain ⟨hs, hStable, hInv⟩ := RealNormalization.LocalAnalysis.real_fourier_analysis N ψ hc hu hn
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ ψ hs
  exact archimedeanWeyl_energy ψ hu hc (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ) hStable hInv f u

theorem complexWeyl_energy {N : ℕ} (ψ : AddChar ℂ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ N) :
    (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure ℂ N) f.val u.val v‖ ^ 2
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ)) =
      Local.FunctionsMetaplectic.Construction.l2Energy ℂ N f * Local.FunctionsMetaplectic.Construction.l2Energy ℂ N u := by
  obtain ⟨hs, hStable, hInv⟩ := ComplexNormalization.LocalAnalysis.complex_fourier_analysis N ψ hc hu hn
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ).IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℂ ψ hs
  exact archimedeanWeyl_energy ψ hu hc (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ) hStable hInv f u

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylEnergy.LocalAnalysis
