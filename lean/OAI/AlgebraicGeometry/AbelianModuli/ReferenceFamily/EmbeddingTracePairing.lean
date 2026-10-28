import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm

/-! # Embedding Trace Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingTracePairing

noncomputable section

/-! Complexification of an actual rational Hermitian trace form gives
its literal matrix blocks at the number-field embeddings. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm
open scoped TensorProduct

variable {E U : Type*} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [AddCommGroup U] [Module ℚ U] [Module E U] [IsScalarTower ℚ E U]
    (e : U ≃ₗ[E] (Fin 3 → E))

omit [NumberField.IsCMField E] in
theorem rankThreeComplexCoordinates_conjugation (u : ComplexMultiplication.WeightOne.CM.Complexification U)
    (σ : E →ₐ[ℚ] ℂ) (i : Fin 3) :
    RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E e (ComplexMultiplication.WeightOne.CM.coefficientConjugation U u) σ i =
      star (RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E e u (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ) i) := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, Pi.add_apply, hu, hv, star_add]
  | tmul z u =>
      rw [ComplexMultiplication.WeightOne.CM.coefficientConjugation_tmul, RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates_tmul, RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates_tmul]
      simp only [ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_apply, star_mul, star_star]
      ring

theorem rankThree_trace_baseChange (ψ : LinearMap.BilinForm ℚ U)
    (H : Matrix (Fin 3) (Fin 3) E) (ξ : E)
    (htrace : ∀ x y : U, ψ x y = Algebra.trace ℚ E
      (ξ * ∑ i, ∑ j, e x i * H i j * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (e y j)))
    (u v : ComplexMultiplication.WeightOne.CM.Complexification U) :
    LinearMap.BilinForm.baseChange ℂ ψ u v =
      ∑ σ : E →ₐ[ℚ] ℂ, σ ξ * ∑ i, ∑ j,
        RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E e u σ i * σ (H i j) *
          RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E e v (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ) j := by
  classical
  induction u using TensorProduct.inductionOn with
  | add u w hu hw =>
      simp only [map_add, LinearMap.add_apply, Pi.add_apply, add_mul, mul_add,
        Finset.sum_add_distrib, hu, hw]
  | tmul z x =>
      induction v using TensorProduct.inductionOn with
      | add v w hv hw =>
          simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, hv, hw]
      | tmul t y =>
          rw [LinearMap.BilinForm.baseChange_tmul, htrace]
          change algebraMap ℚ ℂ (Algebra.trace ℚ E
            (ξ * ∑ i, ∑ j, e x i * H i j * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (e y j))) * (z * t) = _
          rw [trace_eq_sum_embeddings ℂ]
          simp only [map_mul, map_sum, ComplexMultiplication.CM.TraceForm.cmFieldConjugation_embedding,
            RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates_tmul, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_apply,
            Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σ _
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring

theorem rankThree_trace_conjugate (ψ : LinearMap.BilinForm ℚ U)
    (H : Matrix (Fin 3) (Fin 3) E) (ξ : E)
    (htrace : ∀ x y : U, ψ x y = Algebra.trace ℚ E
      (ξ * ∑ i, ∑ j, e x i * H i j * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (e y j)))
    (u v : ComplexMultiplication.WeightOne.CM.Complexification U) :
    LinearMap.BilinForm.baseChange ℂ ψ u (ComplexMultiplication.WeightOne.CM.coefficientConjugation U v) =
      ∑ σ : E →ₐ[ℚ] ℂ, σ ξ * ∑ i, ∑ j,
        RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E e u σ i * σ (H i j) *
          star (RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E e v σ j) := by
  rw [rankThree_trace_baseChange e ψ H ξ htrace]
  simp only [rankThreeComplexCoordinates_conjugation, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingTracePairing
