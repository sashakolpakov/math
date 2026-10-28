import OAI.Geometry.ComplexBall.PrescribedSignsB
import OAI.NumberTheory.Approximation.Weak

/-! # Prescribed Signs Weak -/

namespace OAI.Geometry.ComplexBall.PrescribedSignsWeak

noncomputable section

open scoped Classical
universe u

lemma weakApproximationInput_proved (E : Type u) [Field E] [NumberField E] :
    PrescribedSignsB.WeakApproximationInput E := by
  intro ι _ v hn hd
  exact NumberTheory.Approximation.Weak.HodgeWeakApproximation.weak_approximation E v hn hd

/-- PrescribedSigns: prescribed compact-place signs admit Hermitian line
forms and holomorphic positive Lagrangians, individually and
for their orthogonal direct sum. -/
theorem lagrangians_with_prescribed_compact_place_signs_unconditional
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
      (∀ i, a i ≠ 0 ∧
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
                NumberField.IsCMField.complexConj E (y k)))) : ℂ)) := by
  exact PrescribedSignsB.lagrangians_with_prescribed_compact_place_signs
    (weakApproximationInput_proved E) σ hσ μ δ hδ hδc H hHermitian hμpos hμneg hcompact d

end

end OAI.Geometry.ComplexBall.PrescribedSignsWeak
