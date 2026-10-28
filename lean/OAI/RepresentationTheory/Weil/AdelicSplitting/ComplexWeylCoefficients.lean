import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexPartialFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexTemperate
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeylCoefficients
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters

/-! # Complex Weyl Coefficients -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexWeylCoefficients.Construction

noncomputable section

/-! Complex Weyl matrix coefficients are actual Schwartz functions. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters.LocalAnalysis _root_.MeasureTheory
open scoped SchwartzMap ComplexConjugate

variable {N : ℕ}

def complexWeylKernel (f h : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℂ N) ℂ) :
    SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℂ N × Local.FunctionsMetaplectic.Construction.Position ℂ N) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (UnitarySplitting.RealWeylCoefficients.Construction.weylKernelCoordinates (Local.FunctionsMetaplectic.Construction.Position ℂ N))
    (UnitarySplitting.SchwartzTensor.Construction.schwartzTensor f (SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap h))

def complexWeylMidpointPhase (v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N) : ℂ := -Local.FunctionsMetaplectic.Construction.dot (UnitarySplitting.FourierCovariance.Construction.phaseMomentum v) (UnitarySplitting.FourierCovariance.Construction.phasePosition v) / 2

theorem complexWeylMidpointPhase_temperate (N : ℕ) :
    Function.HasTemperateGrowth (complexWeylMidpointPhase (N := N)) := by
  let P : Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N →L[ℝ] Local.FunctionsMetaplectic.Construction.Position ℂ N := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inr i)
  let Q : Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N →L[ℝ] Local.FunctionsMetaplectic.Construction.Position ℂ N := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inl i)
  convert! (ComplexTemperate.Construction.complex_dot_temperate P Q P.hasTemperateGrowth Q.hasTemperateGrowth).neg.mul
    (Function.HasTemperateGrowth.const (2 : ℂ)⁻¹) using 1

def complexWeylFrequencyCoordinates (b : ℂ) (hb : b ≠ 0) :
    Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N ≃L[ℝ] (Local.FunctionsMetaplectic.Construction.Position ℂ N × Local.FunctionsMetaplectic.Construction.Position ℂ N) :=
  (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin N) (Fin N) (fun _ => ℂ)).trans
    ((ContinuousLinearEquiv.refl ℝ (Local.FunctionsMetaplectic.Construction.Position ℂ N)).prodCongr
      ((LinearEquiv.smulOfUnit (Units.mk0 (-b) (neg_ne_zero.mpr hb)) :
        Local.FunctionsMetaplectic.Construction.Position ℂ N ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.Position ℂ N).toContinuousLinearEquiv.restrictScalars ℝ))

def complexWeylCoefficientSchwartz (b : ℂ) (hb : b ≠ 0)
    (f h : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℂ N) ℂ) : SchwartzMap (Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun v => ComplexNormalization.LocalAnalysis.complexCharacter b (complexWeylMidpointPhase v))
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexWeylFrequencyCoordinates b hb)
      (ComplexPartialFourier.Construction.complexPartialFourier (complexWeylKernel f h)))

theorem complexCharacter_continuous (b : ℂ) : Continuous (ComplexNormalization.LocalAnalysis.complexCharacter b) := by
  change Continuous (fun z : ℂ => (Real.fourierChar (1 * (b * z).re) : ℂ))
  fun_prop

theorem complexCharacter_norm (b z : ℂ) : ‖ComplexNormalization.LocalAnalysis.complexCharacter b z‖ = 1 := Circle.norm_coe _

theorem complexWeylCoefficientSchwartz_apply (b : ℂ) (hb : b ≠ 0)
    (f h : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℂ N) ℂ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N) :
    complexWeylCoefficientSchwartz b hb f h v = UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient (ComplexNormalization.LocalAnalysis.complexCharacter b) volume f h v := by
  have hphase : Function.HasTemperateGrowth (fun v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N =>
      ComplexNormalization.LocalAnalysis.complexCharacter b (complexWeylMidpointPhase v)) :=
    (ComplexTemperate.Construction.continuous_unitary_complex_character_temperate (ComplexNormalization.LocalAnalysis.complexCharacter b)
    (complexCharacter_continuous b) (complexCharacter_norm b)).comp (complexWeylMidpointPhase_temperate N)
  rw [complexWeylCoefficientSchwartz, SchwartzMap.smulLeftCLM_apply_apply hphase]
  change ComplexNormalization.LocalAnalysis.complexCharacter b (complexWeylMidpointPhase v) *
    ComplexPartialFourier.Construction.complexPartialFourier (complexWeylKernel f h) (UnitarySplitting.FourierCovariance.Construction.phasePosition v, (-b) • UnitarySplitting.FourierCovariance.Construction.phaseMomentum v) = _
  rw [ComplexPartialFourier.Construction.complexPartialFourier_apply, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    have hf : ComplexFourier.LocalAnalysis.complexStandardCharacter (-Local.FunctionsMetaplectic.Construction.dot ((-b) • UnitarySplitting.FourierCovariance.Construction.phaseMomentum v) x) =
        ComplexNormalization.LocalAnalysis.complexCharacter b (Local.FunctionsMetaplectic.Construction.dot (UnitarySplitting.FourierCovariance.Construction.phaseMomentum v) x) := by
      change ComplexFourier.LocalAnalysis.complexStandardCharacter (-Local.FunctionsMetaplectic.Construction.dot ((-b) • UnitarySplitting.FourierCovariance.Construction.phaseMomentum v) x) =
        ComplexFourier.LocalAnalysis.complexStandardCharacter (b * Local.FunctionsMetaplectic.Construction.dot (UnitarySplitting.FourierCovariance.Construction.phaseMomentum v) x)
      congr 1
      simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.smul_apply, smul_eq_mul, neg_mul, Finset.sum_neg_distrib, neg_neg,
        mul_assoc, Finset.mul_sum]
    change ComplexNormalization.LocalAnalysis.complexCharacter b (complexWeylMidpointPhase v) *
      (ComplexFourier.LocalAnalysis.complexStandardCharacter (-Local.FunctionsMetaplectic.Construction.dot ((-b) • UnitarySplitting.FourierCovariance.Construction.phaseMomentum v) x) *
        (f (x - UnitarySplitting.FourierCovariance.Construction.phasePosition v) * conj (h x))) = _
    rw [hf, ← mul_assoc, ← AddChar.map_add_eq_mul]
    have hp : complexWeylMidpointPhase v + Local.FunctionsMetaplectic.Construction.dot (UnitarySplitting.FourierCovariance.Construction.phaseMomentum v) x =
        ∑ i, v (Sum.inr i) * (x i - v (Sum.inl i) / 2) := by
      simp only [complexWeylMidpointPhase, Local.FunctionsMetaplectic.Construction.dot, UnitarySplitting.FourierCovariance.Construction.phaseMomentum, UnitarySplitting.FourierCovariance.Construction.phasePosition,
        mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib, ← Finset.sum_div]
      ring
    rw [hp]
    exact (mul_assoc _ _ _).symm

theorem exists_complex_weyl_coefficient_schwartz
    (ψ : AddChar ℂ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position ℂ N)) [μ.IsAddHaarMeasure] (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ N) :
    ∃ C : SchwartzMap (Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N) ℂ, ∀ v, C v = UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val v := by
  obtain ⟨b, hb, rfl⟩ := ComplexNormalization.LocalAnalysis.continuous_nontrivial_unitary_complex_character ψ hc hu hn
  obtain ⟨φ, hφ⟩ := ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mp f.property
  obtain ⟨η, hη⟩ := ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mp h.property
  let r := Measure.addHaarScalarFactor μ (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℂ N))
  have hμ : μ = r • (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℂ N)) := Measure.isAddLeftInvariant_eq_smul_of_regular μ volume
  refine ⟨(r : ℂ) • complexWeylCoefficientSchwartz b hb φ η, fun v => ?_⟩
  change (r : ℂ) * complexWeylCoefficientSchwartz b hb φ η v = _
  rw [complexWeylCoefficientSchwartz_apply]
  simp only [UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient]
  rw [hμ, integral_smul_nnreal_measure]
  change (r : ℂ) * _ = (r : ℂ) * _
  congr 1
  rw [← hφ, ← hη]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexWeylCoefficients.Construction
