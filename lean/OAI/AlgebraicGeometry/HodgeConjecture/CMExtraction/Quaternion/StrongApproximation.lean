import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.RealSplit
import OAI.NumberTheory.Quaternion.Arithmetic.StrongApproximation
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison

/-! # Strong Approximation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.StrongApproximation

noncomputable section

/-! Proved quaternion strong approximation with the noncompactness
condition derived from a positive real second coefficient. -/

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem quaternion_finite_strongApproximation_positive
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : NumberField.InfinitePlace F)
    (e : NumberTheory.Quaternion.Arithmetic.LocalAdeles.Completion (Sum.inl v : NumberTheory.Quaternion.Arithmetic.LocalAdeles.Place F) ≃+* ℝ) (he : Continuous e)
    (hpos : 0 < e (NumberTheory.Quaternion.Arithmetic.LocalAdeles.localEmbedding (Sum.inl v) b)) :
    DenseRange (NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.diagonalFiniteAdelic (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a b)) := by
  let : CharZero (NumberTheory.Quaternion.Arithmetic.LocalAdeles.Completion (Sum.inl v : NumberTheory.Quaternion.Arithmetic.LocalAdeles.Place F)) :=
    charZero_of_injective_ringHom (NumberTheory.Quaternion.Arithmetic.LocalAdeles.localEmbedding (Sum.inl v : NumberTheory.Quaternion.Arithmetic.LocalAdeles.Place F)).injective
  apply NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.denseRange_diagonalFiniteAdelic_of_away
  apply NumberTheory.Quaternion.Arithmetic.StrongApproximation.strongApproximation_quaternion a b ha hb NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.allArchimedeanPlaces NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.mem_allArchimedeanPlaces
  exact ⟨Sum.inl v, NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.mem_allArchimedeanPlaces v,
    RealSplit.quaternionPoints_noncompact_of_positive_real a b (NumberTheory.Quaternion.Arithmetic.LocalAdeles.localEmbedding (Sum.inl v)) e he ha hb hpos⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.StrongApproximation
