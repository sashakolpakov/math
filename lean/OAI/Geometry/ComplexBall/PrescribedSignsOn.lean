import OAI.Geometry.ComplexBall.NormalizationAdapter
import OAI.Geometry.ComplexBall.DualTransport
import OAI.Geometry.ComplexBall.PrescribedSignsTransportHolomorphic

/-! # Prescribed Signs On -/

namespace OAI.Geometry.ComplexBall.PrescribedSignsOn.Intrinsic

noncomputable section

/-! Complete PrescribedSigns entry point. The public existence theorem is
`PrescribedSigns.lagrangians_with_prescribed_compact_place_signs_native`.
The imported transport theorems identify its tensors, rational forms,
holomorphic families, quotient duals and normalized upstream data. -/

open scoped Classical

variable {E Place : Type*} [Field E] [Algebra ℚ E] [NumberField E]
  [NumberField.IsCMField E] [Fintype Place]

lemma sumForm_skew (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (δ : E) (a : Fin 2 → E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : ∀ i, NumberField.IsCMField.complexConj E (a i) = a i)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (x y : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (PrescribedSignsPeriodTransport.Intrinsic.SumTensor E)) :
    (PrescribedSignsTransportHolomorphic.Intrinsic.rationalSumForm δ a H).baseChange ℂ y x = -(PrescribedSignsTransportHolomorphic.Intrinsic.rationalSumForm δ a H).baseChange ℂ x y := by
  rw [PrescribedSignsTransportHolomorphic.Intrinsic.sumForm_transport σ hσ δ a hδ ha H hH y x,
    PrescribedSignsTransportHolomorphic.Intrinsic.sumForm_transport σ hσ δ a hδ ha H hH x y,
    PrescribedSignsPeriodTransport.Intrinsic.coordinateForm_skew _ _ (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ x).1 (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ y).1,
    PrescribedSignsPeriodTransport.Intrinsic.coordinateForm_skew _ _ (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ x).2 (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ y).2]
  exact (neg_add _ _).symm

lemma lineRiemann_on_real (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (δ a : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (r : ℕ) (P : Submodule ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (PrescribedSignsPeriodTransport.Intrinsic.LineTensor E)))
    (hp : PrescribedSignsB.PositivePeriod r (fun x y => (PrescribedSignsPeriodTransport.Intrinsic.rationalLineForm δ a H).baseChange ℂ x y)
      (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (PrescribedSignsPeriodTransport.Intrinsic.LineTensor E)) P)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (PrescribedSignsPeriodTransport.Intrinsic.LineTensor E))
    (hx : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (PrescribedSignsPeriodTransport.Intrinsic.LineTensor E) x = x) (hne : x ≠ 0) :
    ∃ j : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (PrescribedSignsPeriodTransport.Intrinsic.LineTensor E), AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (PrescribedSignsPeriodTransport.Intrinsic.LineTensor E) j = j ∧
      P.mkQ j = Complex.I • P.mkQ x ∧ 0 < (-(PrescribedSignsPeriodTransport.Intrinsic.rationalLineForm δ a H).baseChange ℂ x j).re :=
  PrescribedSignsPeriodTransport.Intrinsic.rationalRiemann_on_real (PrescribedSignsPeriodTransport.Intrinsic.rationalLineForm δ a H)
    (PrescribedSignsPeriodTransport.Intrinsic.lineForm_skew σ hσ δ a hδ ha H hH) r P hp x hx hne

lemma sumRiemann_on_real (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (δ : E) (a : Fin 2 → E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : ∀ i, NumberField.IsCMField.complexConj E (a i) = a i)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (r : ℕ) (P : Submodule ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (PrescribedSignsPeriodTransport.Intrinsic.SumTensor E)))
    (hp : PrescribedSignsB.PositivePeriod r (fun x y => (PrescribedSignsTransportHolomorphic.Intrinsic.rationalSumForm δ a H).baseChange ℂ x y)
      (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (PrescribedSignsPeriodTransport.Intrinsic.SumTensor E)) P)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (PrescribedSignsPeriodTransport.Intrinsic.SumTensor E))
    (hx : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (PrescribedSignsPeriodTransport.Intrinsic.SumTensor E) x = x) (hne : x ≠ 0) :
    ∃ j : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (PrescribedSignsPeriodTransport.Intrinsic.SumTensor E), AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (PrescribedSignsPeriodTransport.Intrinsic.SumTensor E) j = j ∧
      P.mkQ j = Complex.I • P.mkQ x ∧ 0 < (-(PrescribedSignsTransportHolomorphic.Intrinsic.rationalSumForm δ a H).baseChange ℂ x j).re :=
  PrescribedSignsPeriodTransport.Intrinsic.rationalRiemann_on_real (PrescribedSignsTransportHolomorphic.Intrinsic.rationalSumForm δ a H)
    (sumForm_skew σ hσ δ a hδ ha H hH) r P hp x hx hne

end

end OAI.Geometry.ComplexBall.PrescribedSignsOn.Intrinsic
