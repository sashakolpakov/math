import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType
import OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.MapDescent

/-! # Definitions -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Definitions.CM

noncomputable section

/-! Definitions used in the CMExtraction statement. -/

open scoped TensorProduct Classical
open OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.MapDescent.CM OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField

/-- Complex span of a coefficient-field subspace after scalar conjugation. -/
def conjugateSpace
    (K : IntermediateField ℚ ℂ)
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (A : Submodule K (K ⊗[ℚ] V))
    (σ : Gal(K/ℚ)) : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification V) :=
  Submodule.span ℂ
    {y | ∃ x ∈ A,
      y = ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K V σ x)}

/-- Values on the id-line of complex scalar combinations of rational
Hodge maps from U(v), modeled by the rational vector space E. -/
def cmIdSpan
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V) :
    Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification V) :=
  Submodule.span ℂ
    {y | ∃ f : E →ₗ[ℚ] V,
      ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) H f ∧
      y = f.baseChange ℂ
        (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1))}

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Definitions.CM
