import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticScalarSupport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalPrimeSupport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FiniteTensorUnitary
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ActivePlace

/-! # Filled Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FilledSupport

noncomputable section

/-! Filling the active CM factor changes the original PEL matrix only
at the rational prime q, including after rational-basis coordinate maps. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

namespace TestTransport

theorem adelicScalarEmbedding_idempotent_at_split
    (F : Type) [Field F] [NumberField F] {q : ℕ} [Fact q.Prime] (σ : F →+* Padic q) :
    AdelicScalarEmbedding.TestTransport.adelicScalarEmbedding F (RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q) (PELModuli.CMPoints.LocalPadic.embeddingPlace σ) = 1 := by
  apply (PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv σ).injective
  exact (AdelicScalarEmbedding.TestTransport.adelicScalarEmbedding_at_split F σ (RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q)).trans
    ((RationalPrimeSupport.TestTransport.rationalPrimeIdempotent_same q).trans (map_one _).symm)

end TestTransport

namespace Approximation
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)

theorem cmFiniteTensor_filled_support
    (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)) (i j : Fin 3) :
    RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q •
      ((FiniteTensorUnitary.Approximation.cmFiniteTensorUnitary E δ hδ hδ0 b hb hb0
        (RestrictedInsert.Approximation.restrictedInsertPlace _ (ActivePlace.Approximation.cmActivePlace E σ) (RestrictedAwaySame.Approximation.restrictedForgetPlace _ (ActivePlace.Approximation.cmActivePlace E σ) g))).val.val i j -
        (FiniteTensorUnitary.Approximation.cmFiniteTensorUnitary E δ hδ hδ0 b hb hb0 g).val.val i j) =
      (FiniteTensorUnitary.Approximation.cmFiniteTensorUnitary E δ hδ hδ0 b hb hb0
        (RestrictedInsert.Approximation.restrictedInsertPlace _ (ActivePlace.Approximation.cmActivePlace E σ) (RestrictedAwaySame.Approximation.restrictedForgetPlace _ (ActivePlace.Approximation.cmActivePlace E σ) g))).val.val i j -
        (FiniteTensorUnitary.Approximation.cmFiniteTensorUnitary E δ hδ hδ0 b hb hb0 g).val.val i j :=
  QuadraticScalarSupport.TestTransport.quadraticAdelicTensorMap_sub_support (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0)
    (RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q) _ _
    (QuadraticScalarSupport.Approximation.finiteSU_filled_difference_supported (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
      (ActivePlace.Approximation.cmActivePlace E σ) g (AdelicScalarEmbedding.TestTransport.adelicScalarEmbedding (maximalRealSubfield E) (RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q))
      (TestTransport.adelicScalarEmbedding_idempotent_at_split (maximalRealSubfield E)
        (σ.comp (algebraMap (maximalRealSubfield E) E))) i j)

end Approximation

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FilledSupport
