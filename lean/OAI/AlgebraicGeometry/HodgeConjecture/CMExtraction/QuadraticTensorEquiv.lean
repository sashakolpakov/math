import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorMap
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicTensorDensity

/-! # Quadratic Tensor Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorEquiv.TestTransport

noncomputable section

/-! An explicit continuous inverse to the completed quadratic map,
obtained by extending the two rational coordinate projections. -/

open scoped Classical _root_.NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] (a : F) (η : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a ≃ₐ[F] E)

def quadraticRealLinear : E →ₗ[ℚ] F :=
  (((QuadraticAlgebra.reₗ a 0).comp η.symm.toLinearMap).toAddMonoidHom).toRatLinearMap

def quadraticImaginaryLinear : E →ₗ[ℚ] F :=
  (((QuadraticAlgebra.imₗ a 0).comp η.symm.toLinearMap).toAddMonoidHom).toRatLinearMap

def quadraticTensorInverse (y : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a) :=
  ⟨(AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F).symm (Finite.CoefficientMaps.TestTransport.finiteCoefficientLinearMap (quadraticRealLinear a η) y),
    (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F).symm (Finite.CoefficientMaps.TestTransport.finiteCoefficientLinearMap (quadraticImaginaryLinear a η) y)⟩

theorem quadraticTensorInverse_continuous : Continuous (quadraticTensorInverse a η) := by
  rw [RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
  exact ⟨(AdelicTensorCoordinates.TestTransport.scalarAdelicTensorHomeomorph F).symm.continuous.comp
    (Finite.CoefficientMaps.TestTransport.finiteCoefficientLinearMap_continuous (quadraticRealLinear a η)),
    (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorHomeomorph F).symm.continuous.comp
    (Finite.CoefficientMaps.TestTransport.finiteCoefficientLinearMap_continuous (quadraticImaginaryLinear a η))⟩

theorem quadraticTensorInverse_rational (x : E) :
    quadraticTensorInverse a η (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E x) =
      RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) a (η.symm x) := by
  apply QuadraticAlgebra.ext
  · change (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F).symm
      (Finite.CoefficientMaps.TestTransport.finiteCoefficientLinearMap (quadraticRealLinear a η) (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E x)) = _
    rw [Finite.CoefficientMaps.TestTransport.finiteCoefficientLinearMap_rational, AdelicTensorDensity.TestTransport.scalarAdelicTensorRingEquiv_symm_rational]
    rfl
  · change (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F).symm
      (Finite.CoefficientMaps.TestTransport.finiteCoefficientLinearMap (quadraticImaginaryLinear a η) (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E x)) = _
    rw [Finite.CoefficientMaps.TestTransport.finiteCoefficientLinearMap_rational, AdelicTensorDensity.TestTransport.scalarAdelicTensorRingEquiv_symm_rational]
    rfl

theorem quadraticTensorInverse_left :
    Function.LeftInverse (quadraticTensorInverse a η) (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η) := by
  let := Finite.LatticeTopology.TestTransport.finiteAdeles_t2 F
  have he : (fun z => quadraticTensorInverse a η (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η z)) = id := by
    apply (AdelicTensorDensity.TestTransport.denseRange_quadraticDiagonal F a).equalizer
      ((quadraticTensorInverse_continuous a η).comp (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_continuous a η))
      continuous_id
    funext z
    change quadraticTensorInverse a η (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η
      (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) a z)) = _
    rw [QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_rational, quadraticTensorInverse_rational, AlgEquiv.symm_apply_apply]
    rfl
  exact congr_fun he

theorem quadraticTensorInverse_right :
    Function.RightInverse (quadraticTensorInverse a η) (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η) := by
  let := Finite.CoefficientTopology.TestTransport.finiteCoefficients_t2 E
  have he : (fun y => QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η (quadraticTensorInverse a η y)) = id := by
    apply (AdelicTensorDensity.TestTransport.denseRange_finiteCoefficientEmbedding E).equalizer
      ((QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_continuous a η).comp (quadraticTensorInverse_continuous a η))
      continuous_id
    funext x
    change QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η (quadraticTensorInverse a η (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E x)) = _
    rw [quadraticTensorInverse_rational, QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_rational, AlgEquiv.apply_symm_apply]
    rfl
  exact congr_fun he

def quadraticAdelicTensorRingEquiv :
    RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a) ≃+* AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E where
  toFun := QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η
  invFun := quadraticTensorInverse a η
  left_inv := quadraticTensorInverse_left a η
  right_inv := quadraticTensorInverse_right a η
  map_add' := map_add (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η)
  map_mul' := map_mul (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap a η)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorEquiv.TestTransport
