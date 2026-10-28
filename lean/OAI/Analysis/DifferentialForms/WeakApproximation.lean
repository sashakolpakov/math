import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType

/-! # Weak Approximation -/

namespace OAI.Analysis.DifferentialForms.WeakApproximation.Local

noncomputable section

/- WeakApproximation is used with its stated completion-valued conclusion. The local targets
are field elements (eventually 0 or 1), so no surjectivity of a completion map
onto ℂ is required. No statement stub is imported. -/

open scoped Classical
open _root_.NumberField

variable {E Place : Type*} [Field E] [Algebra ℚ E] [NumberField E]
  [Fintype Place]

/-- The supplied WeakApproximation proposition, specialized to E and the finite place set. -/
def WeakApproximationInput : Prop :=
  ∀ (v : Place → AbsoluteValue E ℝ),
    (∀ i, (v i).IsNontrivial) →
    (Pairwise fun i j => ¬ (v i).IsEquiv (v j)) →
    DenseRange (fun x : E => fun i : Place => (x : (v i).Completion))

omit [NumberField E] [Fintype Place] in
lemma distinct_places
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Injective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1)) :
    Function.Injective (fun τ => InfinitePlace.mk (σ τ).toRingHom) := by
  intro u v huv
  rcases InfinitePlace.mk_eq_iff.mp huv with h | h
  · have he : σ u = σ v := by
      ext x
      exact congrArg (fun f : E →+* ℂ => f x) h
    have hp : (u, false) = (v, false) := hσ (show (if (false : Bool) then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ u) else σ u) =
        (if (false : Bool) then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ v) else σ v) from he)
    exact congrArg Prod.fst hp
  · have he : AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ u) = σ v := by
      ext x
      exact congrArg (fun f : E →+* ℂ => f x) h
    have hp : (u, true) = (v, false) := hσ (show (if (true : Bool) then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ u) else σ u) =
        (if (false : Bool) then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ v) else σ v) from he)
    have hb := congrArg Prod.snd hp
    cases hb

omit [NumberField E] in
lemma approximate_local_field_elements
    (hWeakApproximation : WeakApproximationInput (E := E) (Place := Place))
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Injective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (target : Place → E) (δ : Place → ℝ) (hδ : ∀ τ, 0 < δ τ) :
    ∃ t : E, ∀ τ, dist (σ τ t) (σ τ (target τ)) < δ τ := by
  let w : Place → InfinitePlace E := fun τ => InfinitePlace.mk (σ τ).toRingHom
  have hw : Function.Injective w := distinct_places σ hσ
  let O : Set ((τ : Place) → (w τ).val.Completion) :=
    {z | ∀ τ, dist (z τ) (target τ : (w τ).val.Completion) < δ τ}
  have ho : IsOpen O := by
    simp only [O, Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro τ
    exact isOpen_lt ((continuous_apply τ).dist continuous_const) continuous_const
  have hn : O.Nonempty := ⟨fun τ => (target τ : (w τ).val.Completion), by
    intro τ
    simpa using hδ τ⟩
  have hd := hWeakApproximation (fun τ => (w τ).val) (fun τ => (w τ).isNontrivial)
    (fun u v huv he => huv (hw (InfinitePlace.eq_iff_isEquiv.mpr he)))
  obtain ⟨t, ht⟩ := hd.exists_mem_open ho hn
  refine ⟨t, fun τ => ?_⟩
  have h := ht τ
  change dist
    ((WithAbs.toAbs (w τ).val t : WithAbs (w τ).val) : (w τ).val.Completion)
    ((WithAbs.toAbs (w τ).val (target τ) : WithAbs (w τ).val) :
      (w τ).val.Completion) < δ τ at h
  rw [UniformSpace.Completion.dist_eq, dist_eq_norm] at h
  change ‖σ τ (t - target τ)‖ < δ τ at h
  simpa only [map_sub, dist_eq_norm] using h

end

end OAI.Analysis.DifferentialForms.WeakApproximation.Local
