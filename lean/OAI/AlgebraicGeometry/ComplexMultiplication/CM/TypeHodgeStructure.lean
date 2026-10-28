import OAI.AlgebraicGeometry.ComplexMultiplication.OddSignSwitch
import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Type Hodge Structure -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure

noncomputable section

/-!
# Weight-one Hodge structures from arbitrary CM types

An odd choice of signs on the complex embeddings of a CM field determines
complementary holomorphic and antiholomorphic subspaces on its actual
rational complexification. Multiplication by the field preserves them.
This constructs the rank-one CM Hodge structures required by the switch
reduction; realizing them by projective abelian varieties is a separate step.
-/

open scoped TensorProduct Classical

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]

/-- A CM type as an odd choice on the actual complex embeddings. -/
abbrev CMEmbeddingType := OddSignSwitch.CM.OddSignPattern (EmbeddingHodgeType.CM.conjugateEmbedding (E := E))

/-- Coefficient conjugation conjugates values and swaps the embedding coordinate. -/
theorem fieldComplexificationEquiv_conjugation (x : WeightOne.CM.Complexification E) (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingDecomposition.CM.fieldComplexificationEquiv E (WeightOne.CM.coefficientConjugation E x) σ =
      star (EmbeddingDecomposition.CM.fieldComplexificationEquiv E x (EmbeddingHodgeType.CM.conjugateEmbedding σ)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, star_add]
  | tmul z a => simp

namespace CMEmbeddingType

variable {E} (ε : CMEmbeddingType E)

/-- The span of the embedding vectors selected by one of the two signs. -/
def subspace (b : Bool) : Submodule ℂ (WeightOne.CM.Complexification E) :=
  Submodule.span ℂ ((EmbeddingDecomposition.CM.fieldEmbeddingBasis E) '' {σ | ε.val σ = b})

/-- Membership is the vanishing of all coordinates with the other sign. -/
theorem mem_subspace_iff (b : Bool) (x : WeightOne.CM.Complexification E) :
    x ∈ ε.subspace b ↔ ∀ σ, EmbeddingDecomposition.CM.fieldComplexificationEquiv E x σ ≠ 0 → ε.val σ = b := by
  rw [CMEmbeddingType.subspace, (EmbeddingDecomposition.CM.fieldEmbeddingBasis E).mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff,
    Set.mem_ofPred_eq, EmbeddingDecomposition.CM.fieldEmbeddingBasis, Module.Basis.ofEquivFun_repr_apply]

/-- The two selected collections form a partition of a basis. -/
theorem subspaces_isCompl (b : Bool) : IsCompl (ε.subspace b) (ε.subspace (!b)) := by
  apply (EmbeddingDecomposition.CM.fieldEmbeddingBasis E).linearIndependent.isCompl_span_image
    (EmbeddingDecomposition.CM.fieldEmbeddingBasis E).span_eq
  have hc : {σ | ε.val σ = !b} = {σ | ε.val σ = b}ᶜ := by
    ext σ
    cases b <;> cases ε.val σ <;> simp
  rw [hc]
  exact isCompl_compl

/-- Oddness of the embedding signs gives the actual coefficient-conjugation condition. -/
theorem conjugate_mem_subspace (b : Bool) (x : WeightOne.CM.Complexification E) :
    WeightOne.CM.coefficientConjugation E x ∈ ε.subspace (!b) ↔ x ∈ ε.subspace b := by
  rw [ε.mem_subspace_iff, ε.mem_subspace_iff]
  constructor
  · intro hx σ hσ
    have hc : EmbeddingDecomposition.CM.fieldComplexificationEquiv E (WeightOne.CM.coefficientConjugation E x)
        (EmbeddingHodgeType.CM.conjugateEmbedding σ) ≠ 0 := by
      rw [fieldComplexificationEquiv_conjugation, EmbeddingHodgeType.CM.conjugateEmbedding_involutive]
      simpa using hσ
    have ht := hx (EmbeddingHodgeType.CM.conjugateEmbedding σ) hc
    rw [ε.property σ] at ht
    simpa only [Bool.not_not] using congrArg Bool.not ht
  · intro hx σ hσ
    have hc : EmbeddingDecomposition.CM.fieldComplexificationEquiv E x (EmbeddingHodgeType.CM.conjugateEmbedding σ) ≠ 0 := by
      rw [fieldComplexificationEquiv_conjugation] at hσ
      simpa using hσ
    have ht := hx (EmbeddingHodgeType.CM.conjugateEmbedding σ) hc
    rw [ε.property σ] at ht
    simpa only [Bool.not_not] using congrArg Bool.not ht

/-- The weight-one structure on the rational vector space underlying the field. -/
def hodgeStructure : WeightOne.CM.WeightOneHodgeStructure E where
  holomorphic := ε.subspace true
  antiholomorphic := ε.subspace false
  complementary := ε.subspaces_isCompl true
  conjugate_mem := ε.conjugate_mem_subspace true

/-- The construction has the prescribed type on every canonical embedding vector. -/
theorem embeddingVector_mem_subspace (b : Bool) (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingDecomposition.CM.embeddingVector E σ ∈ ε.subspace b ↔ ε.val σ = b := by
  rw [← EmbeddingDecomposition.CM.fieldEmbeddingBasis_apply, CMEmbeddingType.subspace]
  exact (EmbeddingDecomposition.CM.fieldEmbeddingBasis E).self_mem_span_image

/-- Multiplication by a field element preserves every selected embedding subspace. -/
theorem scalarEndomorphism_preserves (a : E) (b : Bool) (x : WeightOne.CM.Complexification E)
    (hx : x ∈ ε.subspace b) : (WeightOne.CM.scalarEndomorphism E a).baseChange ℂ x ∈ ε.subspace b := by
  rw [ε.mem_subspace_iff] at hx ⊢
  intro σ hσ
  apply hx σ
  intro hz
  apply hσ
  rw [EmbeddingDecomposition.CM.fieldComplexificationEquiv_scalar, hz, mul_zero]

/-- An arbitrary CM embedding type gives a genuine rank-one action on this Hodge structure. -/
theorem rankOneCMAction [NumberField.IsCMField E] : WeightOne.CM.RankOneCMAction E ε.hodgeStructure where
  rank_one := Module.finrank_self E
  hodge_action a x hx := ε.scalarEndomorphism_preserves a true x hx

include ε in
/-- The simultaneous eigenspace is the prescribed canonical embedding line. -/
theorem embeddingSpace_eq_span [NumberField.IsCMField E] (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingDecomposition.CM.embeddingSpace E E σ = ℂ ∙ EmbeddingDecomposition.CM.embeddingVector E σ :=
  eq_span_singleton_of_mem_of_finrank_eq_one (ε.rankOneCMAction.embeddingSpace_finrank σ)
    ((EmbeddingDecomposition.CM.mem_embeddingSpace E E σ _).mpr (fun a => EmbeddingDecomposition.CM.embeddingVector_eigen E a σ))
    (EmbeddingDecomposition.CM.embeddingVector_ne_zero E σ)

/-- Recomputing the Hodge signs from the field action recovers the input CM type. -/
theorem embeddingSign_eq [NumberField.IsCMField E] (σ : E →ₐ[ℚ] ℂ) :
    ε.rankOneCMAction.embeddingSign σ = ε.val σ := by
  apply Bool.eq_iff_iff.mpr
  simp only [WeightOne.CM.RankOneCMAction.embeddingSign, decide_eq_true_eq]
  rw [ε.embeddingSpace_eq_span, Submodule.span_singleton_le_iff_mem]
  exact ε.embeddingVector_mem_subspace true σ

end CMEmbeddingType

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure
