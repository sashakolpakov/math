import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPhasePlancherel
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylEnergy
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedWeakAnalysis
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakCayleyCoefficients

/-! # Archimedean Cayley Energy -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCayleyEnergy.Construction

noncomputable section

/-! Exact coefficient energy of the corrected archimedean weak Cayley
integral. All Fourier and orthogonality inputs are discharged below for
the real and complex local fields. -/

open _root_.MeasureTheory
open scoped NNReal _root_.Matrix

theorem openCellScale_eq_sqrt_haarModulus
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] {N : ℕ}
    (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) :
    Normalization.Construction.openCellScale k N g = Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k (g.val - 1).det : ℝ) := by
  rw [Normalization.Construction.openCellScale, dite_eq_left hg]
  congr 1
  exact congrArg (fun z : ℝ≥0 => (z : ℝ))
    (DeterminantMeasure.LocalAnalysis.haarModulus_unit k (Units.mk0 (g.val - 1).det hg)).symm

theorem correctedWeakOpenCell_coefficient_energy
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
    (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (μ : Measure k) [μ.IsAddHaarMeasure]
    (W : Oscillator.Construction.LocalCover k N ψ) (hW : Oscillator.Construction.localProjection k N ψ W = Local.Generators.Construction.weylSymplectic k N)
    (hP : ∀ a : RapidFunctions.LocalAnalysis.RapidFunction (Local.FunctionsMetaplectic.Construction.PhaseSpace k N),
      (∫ v, ‖∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing k N v w) * a w
        ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)‖ ^ 2 ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) =
        ∫ v, ‖a v‖ ^ 2 ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ))
    (hMoyal : ∀ f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
      (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val u.val v‖ ^ 2
        ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) = Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N u)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (∫ v, ‖CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) g hg
      f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val‖ ^ 2
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) = Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N u := by
  let ν := Measure.pi (fun _ : Fin N ⊕ Fin N => μ)
  let D := SchrodingerPairing.Construction.openCellDifference k N g hg
  let q := SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg
  let C := ArchimedeanWeylCoefficients.LocalAnalysis.archimedeanWeylCoefficientRapid hk ψ hc hu W hW f u
  let φ := C.unitPhase (fun v => ψ (q v))
    (hc.comp (CorrectedWeakAnalysis.Construction.schrodingerCayleyPhase_continuous N g hg)) (fun v => hu _)
  let T : Local.FunctionsMetaplectic.Construction.PhaseSpace k N → ℂ := fun v => ∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing k N v w) * φ w ∂ν
  have hT : (∫ v, ‖T v‖ ^ 2 ∂ν) = Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N u := by
    rw [hP φ]
    have he (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) : ‖φ v‖ = ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
        f.val u.val v‖ := by
      change ‖ψ (q v) * UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val u.val v‖ = _
      rw [norm_mul, hu, one_mul]
    simp_rw [he]
    exact hMoyal f u
  have hA (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
      CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val =
        (Normalization.Construction.openCellScale k N g : ℂ)⁻¹ * (ψ (q v) * T (D.symm v)) := by
    unfold CorrectedNormalization.Construction.correctedWeakOpenCell SchrodingerPairing.Construction.schrodingerCayleyPhase
    rw [CorrectedNormalization.Construction.schrodingerPairing_eq_standardBilinear]
    rw [UnitarySplitting.WeakCayleyCoefficients.Construction.weakCayleyGaussian_output_coefficient hk ψ hc hu ν
      (CorrectedNormalization.Construction.standardSymplecticOfMatrix k N g) D (SchrodingerPairing.Construction.openCellDifference_apply k N g hg)]
    unfold T φ q C RapidFunctions.LocalAnalysis.RapidFunction.unitPhase
    simp only [SchrodingerPairing.Construction.schrodingerCayleyPhase, CorrectedNormalization.Construction.schrodingerPairing_eq_standardBilinear]
    rfl
  have hD (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) : D.symm v = (g.val - 1)⁻¹ *ᵥ v := by
    change (Matrix.toLin (Pi.basisFun k (Fin N ⊕ Fin N))
      (Pi.basisFun k (Fin N ⊕ Fin N)) (g.val - 1)⁻¹) v = _
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  have hs : 0 < Normalization.Construction.openCellScale k N g := by
    rw [openCellScale_eq_sqrt_haarModulus g hg]
    exact Real.sqrt_pos.mpr (DeterminantMeasure.LocalAnalysis.haarModulus_pos k hg)
  have hs2 : Normalization.Construction.openCellScale k N g ^ 2 = (DeterminantMeasure.LocalAnalysis.haarModulus k (g.val - 1).det : ℝ) := by
    rw [openCellScale_eq_sqrt_haarModulus g hg]
    exact Real.sq_sqrt (DeterminantMeasure.LocalAnalysis.haarModulus_pos k hg).le
  change (∫ v, ‖CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg
    f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val‖ ^ 2 ∂ν) = _
  simp_rw [hA, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
    hu, one_mul, mul_pow, hD]
  have hc0 : (DeterminantMeasure.LocalAnalysis.haarModulus k (g.val - 1).det : ℝ) ≠ 0 := by
    exact_mod_cast (DeterminantMeasure.LocalAnalysis.haarModulus_pos k hg).ne'
  rw [integral_const_mul, PhaseMeasure.Construction.phaseMatrix_inverse_integral k μ (g.val - 1) hg (fun v => ‖T v‖ ^ 2),
    hT, inv_pow, hs2, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

theorem correctedWeakOpenCell_real_coefficient_energy {N : ℕ}
    (hk : ¬ DiscreteTopology ℝ) (ψ : AddChar ℝ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic ℝ N) (hg : (g.val - 1).det ≠ 0) (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) :
    (∫ v, ‖CorrectedNormalization.Construction.correctedWeakOpenCell ℝ N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ))
      g hg f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val‖ ^ 2
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ)) =
      Local.FunctionsMetaplectic.Construction.l2Energy ℝ N f * Local.FunctionsMetaplectic.Construction.l2Energy ℝ N u := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ ψ
    (RealNormalization.LocalAnalysis.real_fourier_analysis N ψ hc hu hn).1
  exact correctedWeakOpenCell_coefficient_energy hk ψ hc hu (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ)
    (RealNormalization.LocalAnalysis.realRawFourierOscillator N ψ hc hu hn) rfl
    (ArchimedeanPhasePlancherel.LocalAnalysis.real_phaseFourier_rapid_energy ψ hc hu hn) (ArchimedeanWeylEnergy.LocalAnalysis.realWeyl_energy ψ hc hu hn) g hg f u

theorem correctedWeakOpenCell_complex_coefficient_energy {N : ℕ}
    (hk : ¬ DiscreteTopology ℂ) (ψ : AddChar ℂ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic ℂ N) (hg : (g.val - 1).det ≠ 0) (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ N) :
    (∫ v, ‖CorrectedNormalization.Construction.correctedWeakOpenCell ℂ N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ))
      g hg f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val‖ ^ 2
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ)) =
      Local.FunctionsMetaplectic.Construction.l2Energy ℂ N f * Local.FunctionsMetaplectic.Construction.l2Energy ℂ N u := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ).IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℂ ψ
    (ComplexNormalization.LocalAnalysis.complex_fourier_analysis N ψ hc hu hn).1
  exact correctedWeakOpenCell_coefficient_energy hk ψ hc hu (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ)
    (ComplexNormalization.LocalAnalysis.complexRawFourierOscillator N ψ hc hu hn) rfl
    (ArchimedeanPhasePlancherel.LocalAnalysis.complex_phaseFourier_rapid_energy ψ hc hu hn) (ArchimedeanWeylEnergy.LocalAnalysis.complexWeyl_energy ψ hc hu hn) g hg f u

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCayleyEnergy.Construction
