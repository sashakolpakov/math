import OAI.Geometry.ComplexBall.PrescribedSignsTransportHolomorphic
import OAI.Geometry.ComplexBall.PrescribedSignsPeriodTransport

/-! # Intrinsic -/

namespace OAI.Geometry.ComplexBall.Intrinsic.PrescribedSigns

noncomputable section

open scoped Classical
universe u

/-- PrescribedSigns: prescribed compact-place signs admit Hermitian line
forms and holomorphic positive Lagrangians, individually and
for their orthogonal direct sum. -/
theorem lagrangians_with_prescribed_compact_place_signs_native
    {E : Type u} {Place : Type*}
    [Field E] [Algebra ℚ E] [NumberField E]
    [IsGalois ℚ E] [NumberField.IsCMField E]
    [Fintype Place]
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective
      (fun p : Place × Bool =>
        if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (μ : Place)
    (δ : E) (hδ : δ ≠ 0)
    (hδc : NumberField.IsCMField.complexConj E δ = -δ)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hHermitian : ∀ j k,
      H j k = NumberField.IsCMField.complexConj E (H k j))
    -- An adapted basis at μ: the first two coordinates are
    -- positive, and the final basis vector is negative.
    (hμpos : ∀ x : PrescribedSignsB.Vec, x ≠ 0 → x 2 = 0 →
      0 < (PrescribedSignsB.localB σ H μ x (star x)).re)
    (hμneg :
      (PrescribedSignsB.localB σ H μ ![0, 0, 1] ![0, 0, 1]).re < 0)
    (hcompact : ∀ τ, τ ≠ μ →
      (∀ x : PrescribedSignsB.Vec, x ≠ 0 →
        0 < (PrescribedSignsB.localB σ H τ x (star x)).re) ∨
      (∀ x : PrescribedSignsB.Vec, x ≠ 0 →
        (PrescribedSignsB.localB σ H τ x (star x)).re < 0))
    (d : Fin 2 → Place → Bool) :
    let B := PrescribedSignsB.localB σ H
    let O : Set PrescribedSignsB.BallChart :=
      {z | (B μ (PrescribedSignsB.lineVector z) (star (PrescribedSignsB.lineVector z))).re < 0}
    let r := 3 * Fintype.card Place
    ∃ (a : Fin 2 → E)
      (ℱ : Fin 2 → PrescribedSignsB.BallChart → Submodule ℂ (PrescribedSignsB.Ambient Place)),
      let ψ : Fin 2 → PrescribedSignsB.Ambient Place → PrescribedSignsB.Ambient Place → ℂ :=
        fun i => PrescribedSignsB.tracePairing B (fun τ => σ τ (δ * a i))
      -- Wᵢ = E, with hᵢ(s,t) = aᵢ s c(t).
      ((∀ i, a i ≠ 0 ∧
        NumberField.IsCMField.complexConj E (a i) = a i ∧
        (σ μ (δ * a i)).im < 0) ∧
      (∀ i, PrescribedSignsB.HolomorphicFamily O r (ℱ i)) ∧
      (∀ i z, z ∈ O →
        (∀ u, u ∈ ℱ i z ↔ PrescribedSignsB.Prescribed B μ (d i) z u) ∧
        PrescribedSignsB.PositivePeriod r (ψ i) PrescribedSignsB.realConj (ℱ i z)) ∧
      -- W = W₁ ⊥ W₂.
      PrescribedSignsB.HolomorphicFamily O (r + r)
        (fun z => (ℱ 0 z).prod (ℱ 1 z)) ∧
      (∀ z, z ∈ O →
        PrescribedSignsB.PositivePeriod (r + r)
          (fun u v => ψ 0 u.1 v.1 + ψ 1 u.2 v.2)
          (fun u => (PrescribedSignsB.realConj u.1, PrescribedSignsB.realConj u.2))
          ((ℱ 0 z).prod (ℱ 1 z))) ∧
      -- Compatibility with the rational trace form.
      (∀ (i : Fin 2) (x y : Fin 3 → E),
        ψ i (PrescribedSignsB.embeddingCoordinates σ x)
          (PrescribedSignsB.embeddingCoordinates σ y) =
        ((Algebra.trace ℚ E
          (δ * a i *
            (∑ j, ∑ k,
              x j * H j k *
                NumberField.IsCMField.complexConj E (y k)))) : ℂ))) ∧
      (letI := PrescribedSignsTransportHolomorphic.Intrinsic.coordinateNorm (PrescribedSignsPeriodTransport.Intrinsic.lineCoordinates σ hσ)
       letI := NormedSpace.induced ℂ _ _ (PrescribedSignsPeriodTransport.Intrinsic.lineCoordinates σ hσ)
       ∀ i, PrescribedSignsB.HolomorphicFamily O r
         (fun z => (ℱ i z).comap (PrescribedSignsPeriodTransport.Intrinsic.lineCoordinates σ hσ).toLinearMap)) ∧
      (∀ i z, z ∈ O → PrescribedSignsB.PositivePeriod r
        (fun x y => (PrescribedSignsPeriodTransport.Intrinsic.rationalLineForm δ (a i) H).baseChange ℂ x y)
        (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (PrescribedSignsPeriodTransport.Intrinsic.LineTensor E))
        ((ℱ i z).comap (PrescribedSignsPeriodTransport.Intrinsic.lineCoordinates σ hσ).toLinearMap)) ∧
      (letI := PrescribedSignsTransportHolomorphic.Intrinsic.coordinateNorm (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ)
       letI := NormedSpace.induced ℂ _ _ (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ)
       PrescribedSignsB.HolomorphicFamily O (r + r)
         (fun z => ((ℱ 0 z).prod (ℱ 1 z)).comap (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ).toLinearMap)) ∧
      (∀ z, z ∈ O → PrescribedSignsB.PositivePeriod (r + r)
        (fun x y => (PrescribedSignsTransportHolomorphic.Intrinsic.rationalSumForm δ a H).baseChange ℂ x y)
        (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (PrescribedSignsPeriodTransport.Intrinsic.SumTensor E))
        (((ℱ 0 z).prod (ℱ 1 z)).comap (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ).toLinearMap)) := by
  obtain ⟨a, ℱ, h⟩ := PrescribedSignsWeak.lagrangians_with_prescribed_compact_place_signs_unconditional
    σ hσ μ δ hδ hδc H hHermitian hμpos hμneg hcompact d
  refine ⟨a, ℱ, h, ?_, ?_, ?_, ?_⟩
  · intro i
    exact PrescribedSignsTransportHolomorphic.Intrinsic.holomorphicFamily_native (PrescribedSignsPeriodTransport.Intrinsic.lineCoordinates σ hσ) _ _ (ℱ i) (h.2.1 i)
  · intro i z hz
    apply PrescribedSignsPeriodTransport.Intrinsic.linePositivePeriod_transport σ hσ δ (a i) hδc (h.1 i).2.1 H hHermitian
    simpa only [PrescribedSignsPeriodTransport.Intrinsic.coordinateForm_apply, PrescribedSignsB.matrixB_apply] using (h.2.2.1 i z hz).2
  · exact PrescribedSignsTransportHolomorphic.Intrinsic.holomorphicFamily_native (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ) _ _ _ h.2.2.2.1
  · intro z hz
    apply PrescribedSignsTransportHolomorphic.Intrinsic.sumPositivePeriod_transport σ hσ δ a hδc (fun i => (h.1 i).2.1) H hHermitian
    simpa only [PrescribedSignsPeriodTransport.Intrinsic.coordinateForm_apply, PrescribedSignsB.matrixB_apply] using h.2.2.2.2.1 z hz

end

end OAI.Geometry.ComplexBall.Intrinsic.PrescribedSigns
