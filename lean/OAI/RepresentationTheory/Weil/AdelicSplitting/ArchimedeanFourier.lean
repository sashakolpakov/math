import OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters
import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexFourier

/-! # Archimedean Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFourier.LocalAnalysis

noncomputable section

/-! Coordinate Fourier Plancherel on L¹ ∩ L², including amplitudes that
have not been shown to be Schwartz functions. -/

open _root_.MeasureTheory
open scoped FourierTransform

theorem real_fourier_coordinates_function {N : ℕ} (f : Local.FunctionsMetaplectic.Construction.Position ℝ N → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ N) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter 1) volume f x =
      𝓕 (f ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ))) (WithLp.toLp 2 x) := by
  rw [Real.fourier_eq]
  rw [← (PiLp.volume_preserving_toLp (Fin N)).integral_comp
    (MeasurableEquiv.toLp 2 (Local.FunctionsMetaplectic.Construction.Position ℝ N)).measurableEmbedding]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [Circle.smul_def, smul_eq_mul, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, RealCharacters.LocalAnalysis.realCharacter,
      MonoidHom.compAddChar_apply, Function.comp_apply, AddChar.mulShift_apply, one_mul]
    change f y * (Real.fourierChar (-(∑ i, x i * y i)) : ℂ) =
      (Real.fourierChar (-(∑ i, x i * y i)) : ℂ) * f y
    exact mul_comm _ _

theorem real_coordinate_fourier_L2 {N : ℕ} {f : Local.FunctionsMetaplectic.Construction.Position ℝ N → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) :
    (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter 1) volume f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  let e := MeasurableEquiv.toLp 2 (Local.FunctionsMetaplectic.Construction.Position ℝ N)
  have hp := PiLp.volume_preserving_toLp (Fin N)
  have hi := hp.symm e
  have hfi : Integrable (f ∘ e.symm) := hi.integrable_comp_of_integrable hf
  have hfm : MemLp (f ∘ e.symm) 2 := hf2.comp_measurePreserving hi
  have hcoords : (f ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ))) = f ∘ e.symm := by
    funext x
    rfl
  simp_rw [real_fourier_coordinates_function]
  rw [hcoords]
  rw [hp.integral_comp e.measurableEmbedding
    (fun y => ‖𝓕 (f ∘ e.symm) y‖ ^ 2), RealCharacters.LocalAnalysis.real_integral_fourier_norm_sq hfi hfm]
  exact hi.integral_comp e.symm.measurableEmbedding (fun x => ‖f x‖ ^ 2)

theorem complexL2Coordinates_measurePreserving (N : ℕ) :
    MeasurePreserving (ComplexFourier.LocalAnalysis.complexL2Coordinates N).symm := by
  refine ⟨(ComplexFourier.LocalAnalysis.complexL2Coordinates N).symm.continuous.measurable, ?_⟩
  change ComplexFourier.LocalAnalysis.complexPositionHaar N = volume
  rw [ComplexFourier.LocalAnalysis.complexPositionHaar_eq, ComplexFourier.LocalAnalysis.complexPositionHaarFactor_one, one_smul]

theorem complex_coordinate_fourier_L2 {N : ℕ} {f : Local.FunctionsMetaplectic.Construction.Position ℂ N → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) :
    (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral ComplexFourier.LocalAnalysis.complexStandardCharacter volume f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  let e := (ComplexFourier.LocalAnalysis.complexL2Coordinates N).symm.toHomeomorph.toMeasurableEquiv
  have hp := complexL2Coordinates_measurePreserving N
  have hi := hp.symm e
  have hfi : Integrable (f ∘ ComplexFourier.LocalAnalysis.complexL2Coordinates N) := hi.integrable_comp_of_integrable hf
  have hfm : MemLp (f ∘ ComplexFourier.LocalAnalysis.complexL2Coordinates N) 2 := hf2.comp_measurePreserving hi
  simp_rw [ComplexFourier.LocalAnalysis.complex_fourier_coordinates, ComplexFourier.LocalAnalysis.complexPositionHaarFactor_one]
  simp only [NNReal.coe_one, Complex.ofReal_one, one_mul]
  rw [hp.integral_comp e.measurableEmbedding
    (fun y => ‖𝓕 (f ∘ ComplexFourier.LocalAnalysis.complexL2Coordinates N) (ComplexFourier.LocalAnalysis.complexConjugation N y)‖ ^ 2),
    (ComplexFourier.LocalAnalysis.complexConjugation N).measurePreserving.integral_comp
      (ComplexFourier.LocalAnalysis.complexConjugation N).toHomeomorph.measurableEmbedding
      (fun y => ‖𝓕 (f ∘ ComplexFourier.LocalAnalysis.complexL2Coordinates N) y‖ ^ 2), RealCharacters.LocalAnalysis.real_integral_fourier_norm_sq hfi hfm]
  exact hi.integral_comp e.symm.measurableEmbedding (fun x => ‖f x‖ ^ 2)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFourier.LocalAnalysis
