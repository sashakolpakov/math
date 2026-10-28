import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicTensorCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientMaps
import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

/-! # Quadratic Tensor Map -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorMap.TestTransport

noncomputable section

/-! Evaluate the completed quadratic algebra in the actual PEL tensor
algebra through the prescribed quadratic presentation of the field. -/

open scoped Classical _root_.NumberField

def quadraticEvaluation {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (a : R) (δ : S) (hδ : δ ^ 2 = ρ a) : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R a →+* S where
  toFun z := ρ z.re + ρ z.im * δ
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul,
      zero_mul, add_zero]
    rw [← hδ]
    ring

theorem quadraticEvaluation_continuous {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] [ContinuousAdd S] [ContinuousMul S]
    (ρ : R →+* S) (hρ : Continuous ρ) (a : R) (δ : S) (hδ : δ ^ 2 = ρ a) :
    Continuous (quadraticEvaluation ρ a δ hδ) :=
  (hρ.comp (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re a)).add
    ((hρ.comp (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im a)).mul continuous_const)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]

def fieldAdelicCoefficient (ρ : F →ₐ[ℚ] E) : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F →+* AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E :=
  (Finite.CoefficientMaps.TestTransport.finiteCoefficientAlgMap ρ).toRingHom.comp (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F).toRingHom

theorem fieldAdelicCoefficient_continuous (ρ : F →ₐ[ℚ] E) : Continuous (fieldAdelicCoefficient ρ) :=
  (Finite.CoefficientMaps.TestTransport.finiteCoefficientAlgMap_continuous ρ).comp (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv_continuous F)

theorem fieldAdelicCoefficient_rational (ρ : F →ₐ[ℚ] E) (x : F) :
    fieldAdelicCoefficient ρ (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) x) =
      AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (ρ x) := by
  change Finite.CoefficientMaps.TestTransport.finiteCoefficientAlgMap ρ (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F _) = _
  rw [AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv_rational, Finite.CoefficientMaps.TestTransport.finiteCoefficientAlgMap_rational]

variable [Algebra F E] (a : F) (η : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a ≃ₐ[F] E)

omit [NumberField F] [NumberField E] in
theorem quadraticPresentation_apply (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) :
    η z = algebraMap F E z.re + algebraMap F E z.im * η (⟨0, 1⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) := by
  have hz : z = algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) z.re +
      algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) z.im * (⟨0, 1⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) := by
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  conv_lhs => rw [hz]
  rw [map_add, map_mul, η.commutes, η.commutes]

omit [NumberField F] [NumberField E] in
theorem quadraticPresentation_root_square :
    η (⟨0, 1⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) ^ 2 = algebraMap F E a := by
  rw [← map_pow]
  have h : (⟨0, 1⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) ^ 2 = algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) a := by
    apply QuadraticAlgebra.ext <;> simp [pow_two]
  rw [h, η.commutes]

theorem quadraticTensorRoot_square :
    AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (η (⟨0, 1⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a)) ^ 2 =
      fieldAdelicCoefficient (algebraMap F E).toRatAlgHom
        (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a) := by
  rw [← map_pow, quadraticPresentation_root_square, fieldAdelicCoefficient_rational]
  rfl

def quadraticAdelicTensorMap :
    RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a) →+* AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E :=
  quadraticEvaluation (fieldAdelicCoefficient (algebraMap F E).toRatAlgHom)
    (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a)
    (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (η (⟨0, 1⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a)))
    (quadraticTensorRoot_square a η)

theorem quadraticAdelicTensorMap_continuous : Continuous (quadraticAdelicTensorMap a η) := by
  let : ContinuousMul (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) := ⟨Finite.CoefficientTopology.TestTransport.finiteCoefficient_mul_continuous E⟩
  exact quadraticEvaluation_continuous _ (fieldAdelicCoefficient_continuous _) _ _ _

theorem quadraticAdelicTensorMap_rational (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) :
    quadraticAdelicTensorMap a η (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) a z) =
      AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (η z) := by
  change fieldAdelicCoefficient (algebraMap F E).toRatAlgHom (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) z.re) +
    fieldAdelicCoefficient (algebraMap F E).toRatAlgHom (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) z.im) *
      AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (η (⟨0, 1⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a)) = _
  rw [fieldAdelicCoefficient_rational, fieldAdelicCoefficient_rational,
    quadraticPresentation_apply a η z, map_add, map_mul]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorMap.TestTransport
