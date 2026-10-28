import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFourier
import OAI.RepresentationTheory.Weil.UnitarySplitting.PartialSchwartzFourier

/-! # Complex Partial Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexPartialFourier.Construction

noncomputable section

/-! Partial Fourier transformation in complex coordinates preserves the
Schwartz space, with the actual standard complex character and Haar measure. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFourier.LocalAnalysis _root_.MeasureTheory
open OAI.RepresentationTheory.Weil.UnitarySplitting.PartialSchwartzFourier.Construction
open scoped SchwartzMap

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {N : ℕ}

def complexPositionPairCoordinates :
    (V × EuclideanSpace ℂ (Fin N)) ≃L[ℝ] (V × Local.FunctionsMetaplectic.Construction.Position ℂ N) :=
  (ContinuousLinearEquiv.refl ℝ V).prodCongr (ComplexFourier.LocalAnalysis.complexL2Coordinates N)

def complexPartialFourier (f : SchwartzMap (V × Local.FunctionsMetaplectic.Construction.Position ℂ N) ℂ) :
    SchwartzMap (V × Local.FunctionsMetaplectic.Construction.Position ℂ N) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((ContinuousLinearEquiv.refl ℝ V).prodCongr
      ((ComplexFourier.LocalAnalysis.complexL2Coordinates N).symm.trans (ComplexFourier.LocalAnalysis.complexConjugation N).toContinuousLinearEquiv))
    (UnitarySplitting.PartialSchwartzFourier.Construction.schwartzPartialFourier (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ complexPositionPairCoordinates f))

theorem complexPartialFourier_apply (f : SchwartzMap (V × Local.FunctionsMetaplectic.Construction.Position ℂ N) ℂ)
    (x : V) (p : Local.FunctionsMetaplectic.Construction.Position ℂ N) :
    complexPartialFourier f (x, p) =
      ∫ y : Local.FunctionsMetaplectic.Construction.Position ℂ N, ComplexFourier.LocalAnalysis.complexStandardCharacter (-Local.FunctionsMetaplectic.Construction.dot p y) * f (x, y) := by
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ complexPositionPairCoordinates f
  change UnitarySplitting.PartialSchwartzFourier.Construction.partialFourierFunction F (x, ComplexFourier.LocalAnalysis.complexConjugation N ((ComplexFourier.LocalAnalysis.complexL2Coordinates N).symm p)) = _
  rw [UnitarySplitting.PartialSchwartzFourier.Construction.partialFourierFunction_integral]
  change (∫ y : EuclideanSpace ℂ (Fin N), (Real.fourierChar (-inner ℝ y
    (ComplexFourier.LocalAnalysis.complexConjugation N ((ComplexFourier.LocalAnalysis.complexL2Coordinates N).symm p))) : ℂ) * F (x, y)) = _
  rw [← (ArchimedeanFourier.LocalAnalysis.complexL2Coordinates_measurePreserving N).integral_comp
    (ComplexFourier.LocalAnalysis.complexL2Coordinates N).symm.toHomeomorph.measurableEmbedding
    (fun y => (Real.fourierChar (-inner ℝ y
      (ComplexFourier.LocalAnalysis.complexConjugation N ((ComplexFourier.LocalAnalysis.complexL2Coordinates N).symm p))) : ℂ) * F (x, y))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [ComplexFourier.LocalAnalysis.complex_inner_conjugation, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    change (Real.fourierChar (-(Local.FunctionsMetaplectic.Construction.dot p y).re) : ℂ) *
      f (x, ComplexFourier.LocalAnalysis.complexL2Coordinates N ((ComplexFourier.LocalAnalysis.complexL2Coordinates N).symm y)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    change (Real.fourierChar (-(Local.FunctionsMetaplectic.Construction.dot p y).re) : ℂ) * f (x, y) =
      (Real.fourierChar (1 * (-Local.FunctionsMetaplectic.Construction.dot p y).re) : ℂ) * f (x, y)
    rw [Complex.neg_re, one_mul]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexPartialFourier.Construction
