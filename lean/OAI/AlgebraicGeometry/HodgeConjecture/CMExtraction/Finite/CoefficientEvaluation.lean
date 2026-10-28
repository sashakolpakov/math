import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientTopology
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TensorEvaluation

/-! # Coefficient Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientEvaluation.TestTransport

noncomputable section

/-! Continuity of tensor evaluation follows from continuity on the
finite-adele scalar factor and finite-dimensional basis expansion. -/

open scoped Classical TensorProduct

variable (E : Type*) [Field E] [NumberField E]
  {S : Type*} [CommRing S] [Algebra ℚ S] [TopologicalSpace S]
  [IsTopologicalRing S]

theorem finiteCoefficientEvaluation_continuous
    (f : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles →ₐ[ℚ] S) (g : E →ₐ[ℚ] S) (hf : Continuous f) :
    Continuous (TensorEvaluation.TestTransport.tensorEvaluation f g) := by
  let b := (Module.finBasis ℚ E).baseChange AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles
  have he (x : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) : TensorEvaluation.TestTransport.tensorEvaluation f g x =
      ∑ i, f (b.equivFun x i) * TensorEvaluation.TestTransport.tensorEvaluation f g (b i) := by
    conv_lhs => rw [← b.sum_equivFun x]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => TensorEvaluation.TestTransport.tensorEvaluation_smul f g _ _)
  have hc : Continuous (fun x : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E =>
      ∑ i, f (b.equivFun x i) * TensorEvaluation.TestTransport.tensorEvaluation f g (b i)) := by
    apply continuous_finsetSum
    intro i _
    exact (hf.comp
      ((continuous_apply i).comp (AbelianModuli.ReferenceFamily.AdelicCoefficientTopology.finiteCoefficientCoordinates_continuous E))).mul continuous_const
  exact hc.congr (fun x => (he x).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientEvaluation.TestTransport
