import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ScalarEmbedding
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorMap
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryDet
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedInsert

/-! # Quadratic Scalar Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QuadraticScalarSupport.CM

noncomputable section

/-! Filling one local unitary factor changes coefficients only at that
place. Scalar idempotents retain that support in the PEL tensor model. -/

open scoped Classical _root_.NumberField

section
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorMap.TestTransport
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ScalarEmbedding.CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]

theorem fieldAdelicCoefficient_scalar (ρ : F →ₐ[ℚ] E) (a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) :
    CMExtraction.QuadraticTensorMap.TestTransport.fieldAdelicCoefficient ρ (Adelic.ScalarEmbedding.CM.adelicScalarEmbedding F a) =
      algebraMap AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) a := by
  change CMExtraction.Finite.CoefficientMaps.TestTransport.finiteCoefficientAlgMap ρ (CMExtraction.AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F
    ((CMExtraction.AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F).symm (algebraMap AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F) a))) = _
  rw [RingEquiv.apply_symm_apply]
  exact (CMExtraction.Finite.CoefficientMaps.TestTransport.finiteCoefficientAlgMap ρ).commutes a

variable [Algebra F E] (d : F) (η : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d ≃ₐ[F] E)

theorem quadraticAdelicTensorMap_scalar (a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) :
    CMExtraction.QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η
      (algebraMap (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d))
        (Adelic.ScalarEmbedding.CM.adelicScalarEmbedding F a)) =
      algebraMap AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) a := by
  change CMExtraction.QuadraticTensorMap.TestTransport.fieldAdelicCoefficient (algebraMap F E).toRatAlgHom (Adelic.ScalarEmbedding.CM.adelicScalarEmbedding F a) +
    CMExtraction.QuadraticTensorMap.TestTransport.fieldAdelicCoefficient (algebraMap F E).toRatAlgHom 0 * _ = _
  rw [map_zero, zero_mul, add_zero, fieldAdelicCoefficient_scalar]

theorem quadraticAdelicTensorMap_support (a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles)
    (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d))
    (hz : algebraMap (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
      (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)) (Adelic.ScalarEmbedding.CM.adelicScalarEmbedding F a) * z = z) :
    a • CMExtraction.QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η z = CMExtraction.QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η z := by
  have h := congrArg (CMExtraction.QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η) hz
  rw [map_mul, quadraticAdelicTensorMap_scalar] at h
  rw [Algebra.smul_def]
  exact h

theorem quadraticAdelicTensorMap_sub_support (a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles)
    (x y : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d))
    (h : algebraMap (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
      (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d))
        (Adelic.ScalarEmbedding.CM.adelicScalarEmbedding F a) * (x - y) = x - y) :
    a • (CMExtraction.QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η x - CMExtraction.QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η y) =
      CMExtraction.QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η x - CMExtraction.QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η y := by
  rw [← map_sub]
  exact quadraticAdelicTensorMap_support d η a (x - y) h

end

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorMap.TestTransport
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ScalarEmbedding.CM
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (F : Type) [Field F] [NumberField F] (d : F)

theorem quadratic_scalar_mul_of_supported (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
    (ha : a v = 1)
    (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d))
    (hz : ∀ w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, w ≠ v → CMExtraction.Finite.UnitaryDet.Approximation.finiteQuadraticEvaluation F d w z = 0) :
    algebraMap (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)) a * z = z := by
  apply CMExtraction.Finite.UnitaryDet.Approximation.finiteQuadraticEvaluation_ext F d
  intro w
  rw [map_mul]
  have he : CMExtraction.Finite.UnitaryDet.Approximation.finiteQuadraticEvaluation F d w
      (algebraMap (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)) a) =
      algebraMap (w.adicCompletion F) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr w)) (a w) := rfl
  rw [he]
  by_cases hw : w = v
  · subst w
    rw [ha, map_one, one_mul]
  · rw [hz w hw, mul_zero]

variable {d} {n : ℕ} (H : (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

theorem finiteSU_filled_difference_supported (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H)
    (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (ha : a v = 1) (i j : Fin n) :
    algebraMap (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)) a *
      (CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix F H (CMExtraction.RestrictedInsert.Approximation.restrictedInsertPlace _ v (CMExtraction.RestrictedAwaySame.Approximation.restrictedForgetPlace _ v g)) i j -
        CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix F H g i j) =
      CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix F H (CMExtraction.RestrictedInsert.Approximation.restrictedInsertPlace _ v (CMExtraction.RestrictedAwaySame.Approximation.restrictedForgetPlace _ v g)) i j -
        CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix F H g i j := by
  apply quadratic_scalar_mul_of_supported F d v a ha
  intro w hw
  rw [map_sub]
  change (CMExtraction.RestrictedInsert.Approximation.restrictedInsertPlace _ v (CMExtraction.RestrictedAwaySame.Approximation.restrictedForgetPlace _ v g) w).val.val i j - (g w).val.val i j = 0
  rw [CMExtraction.RestrictedInsert.Approximation.restrictedInsertPlace_other _ v _ w hw]
  exact sub_self _

theorem finiteSU_difference_supported (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (g h : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H)
    (he : ∀ w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, w ≠ v → h w = g w)
    (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (ha : a v = 1) (i j : Fin n) :
    algebraMap (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)) a *
      (CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix F H h i j - CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix F H g i j) =
      CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix F H h i j - CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix F H g i j := by
  apply quadratic_scalar_mul_of_supported F d v a ha
  intro w hw
  rw [map_sub]
  change (h w).val.val i j - (g w).val.val i j = 0
  rw [he w hw, sub_self]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QuadraticScalarSupport.CM
