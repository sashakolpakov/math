import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicEmbeddingPlace

/-! # Place Fibers -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.PlaceFibers.Approximation

noncomputable section

/-! Two CM embeddings define the same finite place of the maximal
real subfield precisely when they agree up to CM conjugation. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {q : ℕ} [Fact q.Prime] (σ τ : E →+* Padic q)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

include hδ hδ0 in
theorem cm_embeddings_eq_or_conjugate
    (hF : σ.comp (algebraMap (maximalRealSubfield E) E) =
      τ.comp (algebraMap (maximalRealSubfield E) E)) :
    σ = τ ∨ σ = τ.comp (IsCMField.complexConj E).toRingHom := by
  have hreal (a : maximalRealSubfield E) : σ (a : E) = τ (a : E) := RingHom.congr_fun hF a
  have hs : σ δ ^ 2 = τ δ ^ 2 := by
    rw [← map_pow, ← map_pow]
    exact hreal (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs
  · left
    ext x
    obtain ⟨z, rfl⟩ := (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).surjective x
    change σ (ThetaCycle.QuadraticModel.CM.cmQuadraticMap E δ hδ z) = τ (ThetaCycle.QuadraticModel.CM.cmQuadraticMap E δ hδ z)
    rw [ThetaCycle.QuadraticModel.CM.cm_quadratic_map_apply, map_add, map_mul, map_add, map_mul, hreal, hreal, hs]
  · right
    ext x
    obtain ⟨z, rfl⟩ := (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).surjective x
    change σ (ThetaCycle.QuadraticModel.CM.cmQuadraticMap E δ hδ z) = τ (IsCMField.complexConj E (ThetaCycle.QuadraticModel.CM.cmQuadraticMap E δ hδ z))
    rw [ThetaCycle.QuadraticModel.CM.cm_quadratic_map_apply, map_add, map_mul, map_add, map_mul,
      IsCMField.complexConj_apply_eq_self, IsCMField.complexConj_apply_eq_self, hδ,
      map_add, map_mul, map_neg, hreal, hreal, hs]

theorem cmActivePlace_conjugate :
    ActivePlace.Approximation.cmActivePlace E (σ.comp (IsCMField.complexConj E).toRingHom) = ActivePlace.Approximation.cmActivePlace E σ := by
  apply congrArg PELModuli.CMPoints.LocalPadic.embeddingPlace
  ext x
  change σ (IsCMField.complexConj E (x : E)) = σ (x : E)
  rw [IsCMField.complexConj_apply_eq_self]

include hδ hδ0 in
theorem cmActivePlace_eq_iff :
    ActivePlace.Approximation.cmActivePlace E σ = ActivePlace.Approximation.cmActivePlace E τ ↔
      σ = τ ∨ σ = τ.comp (IsCMField.complexConj E).toRingHom := by
  constructor
  · intro h
    exact cm_embeddings_eq_or_conjugate E σ τ δ hδ hδ0
      (PadicEmbeddingPlace.Approximation.padic_embeddingPlace_injective (maximalRealSubfield E) h)
  · rintro (h | h)
    · exact congrArg (ActivePlace.Approximation.cmActivePlace E) h
    · rw [h, cmActivePlace_conjugate]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.PlaceFibers.Approximation
