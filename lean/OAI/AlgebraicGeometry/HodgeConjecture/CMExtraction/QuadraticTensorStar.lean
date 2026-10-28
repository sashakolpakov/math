import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientConjugation

/-! # Quadratic Tensor Star -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorStar.TestTransport

noncomputable section

/-! The completed quadratic comparison preserves the actual CM
conjugation whenever its specified rational presentation does. -/

open scoped Classical _root_.NumberField

open _root_.NumberField

theorem quadraticBaseChange_star {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : R) (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R a) :
    RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange f a (star z) = star (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange f a z) := by
  apply QuadraticAlgebra.ext
  · change f (star z).re = (star (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange f a z)).re
    simp only [QuadraticAlgebra.re_star, zero_mul, add_zero]
    rfl
  · change f (star z).im = (star (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange f a z)).im
    simp only [QuadraticAlgebra.im_star]
    exact map_neg f z.im

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsCMField E] (a : F) (η : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a ≃ₐ[F] E)

theorem quadraticAdelicTensorMap_star
    (hη : ∀ z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a, η (star z) = IsCMField.complexConj E (η z))
    (x : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a)) :
    QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η (star x) = star (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η x) := by
  let := Finite.CoefficientTopology.TestTransport.finiteCoefficients_t2 E
  have he : (fun y => QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η (star y)) =
      (fun y => star (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η y)) := by
    apply (AdelicTensorDensity.TestTransport.denseRange_quadraticDiagonal F a).equalizer
      ((QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_continuous a η).comp continuous_star)
      (continuous_star.comp (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_continuous a η))
    funext z
    change QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η
      (star (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) a z)) =
      star (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) a z))
    rw [← quadraticBaseChange_star, QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_rational,
      QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_rational, Finite.CoefficientConjugation.TestTransport.finiteCoefficientEmbedding_star, hη]
  exact congr_fun he x

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorStar.TestTransport
