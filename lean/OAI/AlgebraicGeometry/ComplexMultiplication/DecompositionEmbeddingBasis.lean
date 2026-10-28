import OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition
import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Algebra.Module.Rat

/-! # Decomposition Embedding Basis -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.ComplexMultiplication.DecompositionEmbeddingBasis.CM.CMDecomposition

/-!
# Embedding basis for a CM decomposition with different fields

Complexification commutes with the actual internal direct sum. Applying the
embedding basis construction on each summand therefore gives a basis of the
whole weight-one space. Its vectors are the images under the actual subspace
inclusions, and their signs retain their geometric Hodge types.
-/

open scoped DirectSum TensorProduct Classical

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {H : WeightOne.CM.WeightOneHodgeStructure U} (D : Decomposition.CM.CMDecomposition H)

local instance (i : Fin D.numberOfComponents) : NumberField (D.component i).field :=
  (D.component i).cm.numberField

/-- The sum of complexified summands is the complexification of the original
space, using the same internal sum map as the rational decomposition. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.complexDirectSumEquiv :
    (⨁ i, WeightOne.CM.Complexification (D.component i).subspace) ≃ₗ[ℂ] WeightOne.CM.Complexification U :=
  (TensorProduct.directSumRight ℚ ℂ ℂ (fun i => (D.component i).subspace)).symm.trans
    (D.linearEquiv.baseChange ℚ ℂ _ _)

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.complexDirectSumEquiv_lof_tmul (i : Fin D.numberOfComponents) (z : ℂ)
    (u : (D.component i).subspace) :
    D.complexDirectSumEquiv
      (DirectSum.lof ℂ _ (fun i => WeightOne.CM.Complexification (D.component i).subspace) i (z ⊗ₜ[ℚ] u)) =
      z ⊗ₜ[ℚ] (u : U) := by
  simp [Decomposition.CM.CMDecomposition.complexDirectSumEquiv]

/-- On an entire complexified component, the map is its actual scalar-extended inclusion. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.complexDirectSumEquiv_lof (i : Fin D.numberOfComponents)
    (x : WeightOne.CM.Complexification (D.component i).subspace) :
    D.complexDirectSumEquiv
      (DirectSum.lof ℂ _ (fun i => WeightOne.CM.Complexification (D.component i).subspace) i x) =
      (D.component i).subspace.subtype.baseChange ℂ x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z u => simp

/-- The basis of one summand indexed by embeddings of that summand's own field. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.componentEmbeddingBasis (i : Fin D.numberOfComponents) :
    Module.Basis ((D.component i).field →ₐ[ℚ] ℂ) ℂ
      (WeightOne.CM.Complexification (D.component i).subspace) :=
  (D.component i).cm.embeddingBasis

/-- Basis indices retain both the component and the embedding of its field. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.EmbeddingIndex := Σ i : Fin D.numberOfComponents, (D.component i).field →ₐ[ℚ] ℂ

instance _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.embeddingIndexFintype : Fintype D.EmbeddingIndex :=
  inferInstanceAs (Fintype (Σ i : Fin D.numberOfComponents, (D.component i).field →ₐ[ℚ] ℂ))

/-- All embedding lines together form a basis of the actual complexified space. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.embeddingBasis : Module.Basis D.EmbeddingIndex ℂ (WeightOne.CM.Complexification U) :=
  (DFinsupp.basis D.componentEmbeddingBasis).map D.complexDirectSumEquiv

/-- Each global basis vector is included from its actual rational Hodge summand. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.embeddingBasis_apply (i : Fin D.numberOfComponents) (σ : (D.component i).field →ₐ[ℚ] ℂ) :
    D.embeddingBasis ⟨i, σ⟩ =
      (D.component i).subspace.subtype.baseChange ℂ (D.componentEmbeddingBasis i σ) := by
  have hb : (DFinsupp.basis D.componentEmbeddingBasis) ⟨i, σ⟩ =
      DirectSum.lof ℂ _ (fun i => WeightOne.CM.Complexification (D.component i).subspace) i
        (D.componentEmbeddingBasis i σ) := by
    simp [DFinsupp.basis, DFinsupp.mapRange.linearEquiv]
    change DFinsupp.mapRange (fun k => (D.componentEmbeddingBasis k).repr.symm)
      (fun k => map_zero _) (DFinsupp.single i (Finsupp.single σ 1)) = _
    rw [DFinsupp.mapRange_single, Module.Basis.repr_symm_single, one_smul]
    rfl
  change D.complexDirectSumEquiv ((DFinsupp.basis D.componentEmbeddingBasis) ⟨i, σ⟩) = _
  rw [hb]
  exact D.complexDirectSumEquiv_lof i _

/-- Each sign is attached to its own field's actual embedding line. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.embeddingSign (j : D.EmbeddingIndex) : Bool :=
  (D.component j.1).cm.embeddingSign j.2

/-- Conjugation acts within each component's embedding set. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.conjugateIndex (j : D.EmbeddingIndex) : D.EmbeddingIndex :=
  ⟨j.1, EmbeddingHodgeType.CM.conjugateEmbedding j.2⟩

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.conjugateIndex_involutive (j : D.EmbeddingIndex) :
    D.conjugateIndex (D.conjugateIndex j) = j := by
  rcases j with ⟨i, σ⟩
  exact congrArg (fun τ => (⟨i, τ⟩ : D.EmbeddingIndex)) (EmbeddingHodgeType.CM.conjugateEmbedding_involutive σ)

/-- Positive signs identify holomorphic basis vectors in the whole space. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.embeddingBasis_holomorphic (j : D.EmbeddingIndex) (hj : D.embeddingSign j = true) :
    D.embeddingBasis j ∈ H.holomorphic := by
  rcases j with ⟨i, σ⟩
  rw [D.embeddingBasis_apply]
  apply (D.component i).inclusion_hodge
  exact ((D.component i).cm.embeddingBasis_mem_holomorphic_iff σ).mpr hj

/-- Negative signs identify antiholomorphic basis vectors in the whole space. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.embeddingBasis_antiholomorphic (j : D.EmbeddingIndex) (hj : D.embeddingSign j = false) :
    D.embeddingBasis j ∈ H.antiholomorphic := by
  rcases j with ⟨i, σ⟩
  rw [D.embeddingBasis_apply]
  apply (D.component i).inclusion_hodge.map_antiholomorphic
  exact ((D.component i).cm.embeddingBasis_mem_antiholomorphic_iff σ).mpr hj

/-- The sign functions remain odd when the decomposition uses different CM fields. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.embeddingSign_conjugate (j : D.EmbeddingIndex) :
    D.embeddingSign (D.conjugateIndex j) = !D.embeddingSign j :=
  (D.component j.1).cm.embeddingSign_conjugate j.2

/-- Every vector has a finite, unique expansion in these actual embedding lines. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.sum_embeddingBasis (x : WeightOne.CM.Complexification U) :
    ∑ j, D.embeddingBasis.repr x j • D.embeddingBasis j = x :=
  D.embeddingBasis.sum_repr x

end AlgebraicGeometry.ComplexMultiplication.DecompositionEmbeddingBasis.CM.CMDecomposition

namespace AlgebraicGeometry.ComplexMultiplication

/-!
# The full weight-one Hodge subspaces in the CM basis

The positive and negative embedding vectors span precisely the given
holomorphic and antiholomorphic subspaces. In particular, the nonzero
coordinates of a pure vector have its assigned Hodge sign.
-/

open scoped Classical

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

section

/-- Select one of the two given weight-one Hodge subspaces by its sign. -/
def WeightOne.CM.WeightOneHodgeStructure.signSubspace (H : WeightOne.CM.WeightOneHodgeStructure U) (b : Bool) :
    Submodule ℂ (WeightOne.CM.Complexification U) := if b then H.holomorphic else H.antiholomorphic

theorem WeightOne.CM.WeightOneHodgeStructure.signSubspace_isCompl (H : WeightOne.CM.WeightOneHodgeStructure U) (b : Bool) :
    IsCompl (H.signSubspace b) (H.signSubspace (!b)) := by
  cases b
  · exact H.complementary.symm
  · exact H.complementary

end

variable {H : WeightOne.CM.WeightOneHodgeStructure U} (D : Decomposition.CM.CMDecomposition H)

theorem Decomposition.CM.CMDecomposition.embeddingBasis_mem_signSubspace (j : D.EmbeddingIndex) :
    D.embeddingBasis j ∈ H.signSubspace (D.embeddingSign j) := by
  cases he : D.embeddingSign j
  · exact D.embeddingBasis_antiholomorphic j he
  · exact D.embeddingBasis_holomorphic j he

/-- Each prescribed Hodge subspace is the span of exactly its embedding basis vectors. -/
theorem Decomposition.CM.CMDecomposition.signSubspace_eq_span_embeddingBasis (b : Bool) :
    H.signSubspace b = Submodule.span ℂ (D.embeddingBasis '' {j | D.embeddingSign j = b}) := by
  apply le_antisymm
  · intro x hx
    let P := (H.signSubspace b).projection (H.signSubspace (!b)) (H.signSubspace_isCompl b)
    have hp : P x = x := Submodule.projection_apply_of_mem_left (H.signSubspace_isCompl b) hx
    have he := congrArg P (D.embeddingBasis.sum_repr x)
    rw [hp] at he
    rw [← he]
    simp only [map_sum, map_smul]
    apply Submodule.sum_mem
    intro j _
    by_cases hj : D.embeddingSign j = b
    · have hm : D.embeddingBasis j ∈ H.signSubspace b :=
        hj ▸ D.embeddingBasis_mem_signSubspace j
      have hb : P (D.embeddingBasis j) = D.embeddingBasis j :=
        Submodule.projection_apply_of_mem_left (H.signSubspace_isCompl b) hm
      rw [hb]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · have hj' : D.embeddingSign j = !b := by
        cases b <;> cases heq : D.embeddingSign j <;> simp_all
      have hm : D.embeddingBasis j ∈ H.signSubspace (!b) :=
        hj' ▸ D.embeddingBasis_mem_signSubspace j
      have hb : P (D.embeddingBasis j) = 0 :=
        Submodule.projection_apply_of_mem_right (H.signSubspace_isCompl b) hm
      rw [hb, smul_zero]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro x ⟨j, hj, rfl⟩
    exact hj ▸ D.embeddingBasis_mem_signSubspace j

/-- A nonzero coordinate of a pure weight-one vector has the same Hodge sign. -/
theorem Decomposition.CM.CMDecomposition.embeddingBasis_repr_sign {b : Bool} {x : WeightOne.CM.Complexification U}
    (hx : x ∈ H.signSubspace b) (j : D.EmbeddingIndex)
    (hj : D.embeddingBasis.repr x j ≠ 0) : D.embeddingSign j = b := by
  rw [D.signSubspace_eq_span_embeddingBasis b] at hx
  exact D.embeddingBasis.mem_span_image.mp hx (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hj))

end AlgebraicGeometry.ComplexMultiplication

end

end OAI
