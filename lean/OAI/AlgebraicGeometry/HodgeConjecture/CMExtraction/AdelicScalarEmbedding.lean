import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicTensorDensity
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientPadic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicEmbeddingPlace

/-! # Adelic Scalar Embedding -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicScalarEmbedding.TestTransport

noncomputable section

/-! The scalar finite adeles in a number field's actual restricted
product, and their value at a specified split completion. -/

open scoped Classical TensorProduct _root_.NumberField
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

theorem finiteCoefficientScalar_continuous :
    Continuous (algebraMap AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F)) := by
  have hc : Continuous (fun a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles => a • (1 : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F)) :=
    (continuous_id : Continuous (fun a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles => a)).smul
      (continuous_const : Continuous (fun _ : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles => (1 : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F)))
  exact hc.congr (fun a => by rw [Algebra.smul_def, mul_one])

def adelicScalarEmbedding : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles →+* RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F :=
  (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F).symm.toRingHom.comp
    (algebraMap AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F))

theorem adelicScalarEmbedding_continuous : Continuous (adelicScalarEmbedding F) :=
  (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorHomeomorph F).symm.continuous.comp (finiteCoefficientScalar_continuous F)

variable {q : ℕ} [Fact q.Prime] (σ : F →+* Padic q)

theorem scalarAdelicTensor_padic (x : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic F σ (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F x) =
      PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv σ (x (PELModuli.CMPoints.LocalPadic.embeddingPlace σ)) := by
  have he : (fun x => Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic F σ (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F x)) =
      (fun x : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F => PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv σ (x (PELModuli.CMPoints.LocalPadic.embeddingPlace σ))) := by
    apply (RepresentationTheory.Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_rational_finiteAdeles F).equalizer
      ((Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic_continuous F σ).comp (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv_continuous F))
      ((PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_continuous σ).comp (RestrictedProduct.continuous_eval _))
    funext a
    dsimp only [Function.comp_apply]
    rw [AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv_rational, Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic_rational]
    exact (PELModuli.CMPoints.LocalPadic.embeddingCompletionHom_coe σ a).symm
  exact congr_fun he x

theorem finiteCoefficientPadic_scalar (a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) :
    Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic F σ (algebraMap AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F) a) =
      RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q a :=
  (Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic_tmul F σ a 1).trans (by rw [map_one, mul_one])

theorem adelicScalarEmbedding_at_split (a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) :
    PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv σ (adelicScalarEmbedding F a (PELModuli.CMPoints.LocalPadic.embeddingPlace σ)) =
      RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q a := by
  have h := scalarAdelicTensor_padic F σ (adelicScalarEmbedding F a)
  have he : AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F (adelicScalarEmbedding F a) =
      algebraMap AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F) a :=
    (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F).apply_symm_apply _
  exact h.symm.trans ((congrArg (Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic F σ) he).trans
    (finiteCoefficientPadic_scalar F σ a))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicScalarEmbedding.TestTransport
