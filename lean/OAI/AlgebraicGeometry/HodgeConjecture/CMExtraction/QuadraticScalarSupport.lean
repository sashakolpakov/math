import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicScalarEmbedding
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorMap
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryDet
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedInsert

/-! # Quadratic Scalar Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticScalarSupport

noncomputable section

/-! Filling one local unitary factor changes coefficients only at that
place. Scalar idempotents retain that support in the PEL tensor model. -/

open scoped Classical _root_.NumberField

namespace TestTransport

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]

theorem fieldAdelicCoefficient_scalar (ρ : F →ₐ[ℚ] E) (a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) :
    QuadraticTensorMap.TestTransport.fieldAdelicCoefficient ρ (AdelicScalarEmbedding.TestTransport.adelicScalarEmbedding F a) =
      algebraMap AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) a := by
  change Finite.CoefficientMaps.TestTransport.finiteCoefficientAlgMap ρ (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F
    ((AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F).symm (algebraMap AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F) a))) = _
  rw [RingEquiv.apply_symm_apply]
  exact (Finite.CoefficientMaps.TestTransport.finiteCoefficientAlgMap ρ).commutes a

variable [Algebra F E] (d : F) (η : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d ≃ₐ[F] E)

theorem quadraticAdelicTensorMap_scalar (a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) :
    QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η
      (algebraMap (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d))
        (AdelicScalarEmbedding.TestTransport.adelicScalarEmbedding F a)) =
      algebraMap AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) a := by
  change QuadraticTensorMap.TestTransport.fieldAdelicCoefficient (algebraMap F E).toRatAlgHom (AdelicScalarEmbedding.TestTransport.adelicScalarEmbedding F a) +
    QuadraticTensorMap.TestTransport.fieldAdelicCoefficient (algebraMap F E).toRatAlgHom 0 * _ = _
  rw [map_zero, zero_mul, add_zero, fieldAdelicCoefficient_scalar]

theorem quadraticAdelicTensorMap_support (a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles)
    (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d))
    (hz : algebraMap (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
      (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)) (AdelicScalarEmbedding.TestTransport.adelicScalarEmbedding F a) * z = z) :
    a • QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η z = QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η z := by
  have h := congrArg (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η) hz
  rw [map_mul, quadraticAdelicTensorMap_scalar] at h
  rw [Algebra.smul_def]
  exact h

theorem quadraticAdelicTensorMap_sub_support (a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles)
    (x y : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d))
    (h : algebraMap (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
      (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d))
        (AdelicScalarEmbedding.TestTransport.adelicScalarEmbedding F a) * (x - y) = x - y) :
    a • (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η x - QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η y) =
      QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η x - QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap d η y := by
  rw [← map_sub]
  exact quadraticAdelicTensorMap_support d η a (x - y) h

end TestTransport

namespace Approximation
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (F : Type) [Field F] [NumberField F] (d : F)

theorem quadratic_scalar_mul_of_supported (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
    (ha : a v = 1)
    (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d))
    (hz : ∀ w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, w ≠ v → Finite.UnitaryDet.Approximation.finiteQuadraticEvaluation F d w z = 0) :
    algebraMap (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)) a * z = z := by
  apply Finite.UnitaryDet.Approximation.finiteQuadraticEvaluation_ext F d
  intro w
  rw [map_mul]
  have he : Finite.UnitaryDet.Approximation.finiteQuadraticEvaluation F d w
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
      (Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix F H (RestrictedInsert.Approximation.restrictedInsertPlace _ v (RestrictedAwaySame.Approximation.restrictedForgetPlace _ v g)) i j -
        Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix F H g i j) =
      Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix F H (RestrictedInsert.Approximation.restrictedInsertPlace _ v (RestrictedAwaySame.Approximation.restrictedForgetPlace _ v g)) i j -
        Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix F H g i j := by
  apply quadratic_scalar_mul_of_supported F d v a ha
  intro w hw
  rw [map_sub]
  change (RestrictedInsert.Approximation.restrictedInsertPlace _ v (RestrictedAwaySame.Approximation.restrictedForgetPlace _ v g) w).val.val i j - (g w).val.val i j = 0
  rw [RestrictedInsert.Approximation.restrictedInsertPlace_other _ v _ w hw]
  exact sub_self _

end Approximation

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticScalarSupport
