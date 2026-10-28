import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingMatrixTransport

/-! # Standard Complex Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.StandardComplexCoordinates

noncomputable section

/-! The identity field marking gives the literal standard embedding
coordinates on the complexification of the original field cube. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingMatrixTransport

theorem rankThreeComplexCoordinates_refl (E : Type) [Field E] [NumberField E]
    (u : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E (LinearEquiv.refl E (Fin 3 → E)) u =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E u := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul c v =>
    funext σ i
    rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates_tmul, AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates_tmul]
    rfl

end

end OAI.RepresentationTheory.Theta.Geometric.StandardComplexCoordinates
