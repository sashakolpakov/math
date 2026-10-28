import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientPadic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FiniteTensorUnitary
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ActiveProjection
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryInverse

/-! # Padic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.Padic.Approximation

noncomputable section

/-! The original PEL tensor evaluation and the prescribed CM local
projection agree on every completed coefficient. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientPadic.TestTransport OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

theorem cmCompletedCoefficient_padic (z) :
    Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E σ (FiniteTensorUnitary.Approximation.cmCompletedCoefficient E δ hδ hδ0 z) =
      ActivePlace.Approximation.cmActiveQuadraticProjection E σ δ hδ hδ0
        (Finite.UnitaryDet.Approximation.finiteQuadraticEvaluation (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)
          (ActivePlace.Approximation.cmActivePlace E σ) z) := by
  have he : (fun z => Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E σ (FiniteTensorUnitary.Approximation.cmCompletedCoefficient E δ hδ hδ0 z)) =
      (fun z => ActivePlace.Approximation.cmActiveQuadraticProjection E σ δ hδ hδ0
        (Finite.UnitaryDet.Approximation.finiteQuadraticEvaluation (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)
          (ActivePlace.Approximation.cmActivePlace E σ) z)) := by
    apply (AdelicTensorDensity.TestTransport.denseRange_quadraticDiagonal (maximalRealSubfield E)
      (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)).equalizer
      ((Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic_continuous E σ).comp (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_continuous _ _))
      ((ActivePlace.Approximation.cmActiveQuadraticProjection_continuous E σ δ hδ hδ0).comp
        (Finite.UnitaryInverse.Approximation.finiteQuadraticEvaluation_continuous (maximalRealSubfield E) (ActivePlace.Approximation.cmActivePlace E σ)))
    funext x
    dsimp only [Function.comp_apply]
    rw [QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_rational, Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic_rational,
      Finite.UnitaryDet.Approximation.finiteQuadraticEvaluation_rational, ActivePlace.Approximation.cmActiveQuadraticProjection_rational]
  exact congr_fun he z

variable (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)

theorem cmFiniteTensorUnitary_padic
    (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)) :
    (FiniteTensorUnitary.Approximation.cmFiniteTensorUnitary E δ hδ hδ0 b hb hb0 g).val.val.map (Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E σ) =
      (ActiveProjection.Approximation.cmActiveSL E σ δ hδ hδ0 (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
        (g (ActivePlace.Approximation.cmActivePlace E σ))).val := by
  rw [FiniteTensorUnitary.Approximation.cmFiniteTensorUnitary_matrix, ActiveProjection.Approximation.cmActiveSL_matrix]
  apply Matrix.ext
  intro i j
  exact cmCompletedCoefficient_padic E σ δ hδ hδ0 _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.Padic.Approximation
