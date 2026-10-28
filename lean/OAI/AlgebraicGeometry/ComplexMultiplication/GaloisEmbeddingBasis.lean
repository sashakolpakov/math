import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisSigns
import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingCoefficientField

/-! # Galois Embedding Basis -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.GaloisEmbeddingBasis.CM.CMDecomposition

noncomputable section

/-!
# A Galois-compatible basis of the actual CM decomposition

The basis of `H¹`'s rational Hodge structure is defined over one finite
Galois CM field, including for decompositions with different component
fields. Scalar conjugation acts on these normalized basis vectors by the
previously constructed permutation of their embedding indices.
-/

open scoped DirectSum TensorProduct Classical

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {H : WeightOne.CM.WeightOneHodgeStructure U} (D : Decomposition.CM.CMDecomposition H)

local instance (i : Fin D.numberOfComponents) : NumberField (D.component i).field :=
  (D.component i).cm.numberField

/-- The internal rational sum still gives the same sum map after coefficient extension. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.coefficientDirectSumEquiv :
    (⨁ i, D.commonCoefficientField ⊗[ℚ] (D.component i).subspace) ≃ₗ[D.commonCoefficientField]
      D.commonCoefficientField ⊗[ℚ] U :=
  (TensorProduct.directSumRight ℚ D.commonCoefficientField D.commonCoefficientField
    (fun i => (D.component i).subspace)).symm.trans
      (D.linearEquiv.baseChange ℚ D.commonCoefficientField _ _)

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.coefficientDirectSumEquiv_lof_tmul (i : Fin D.numberOfComponents)
    (z : D.commonCoefficientField) (u : (D.component i).subspace) :
    D.coefficientDirectSumEquiv
      (DirectSum.lof D.commonCoefficientField _
        (fun i => D.commonCoefficientField ⊗[ℚ] (D.component i).subspace) i (z ⊗ₜ[ℚ] u)) =
      z ⊗ₜ[ℚ] (u : U) := by
  simp [Decomposition.CM.CMDecomposition.coefficientDirectSumEquiv]

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.coefficientDirectSumEquiv_lof (i : Fin D.numberOfComponents)
    (x : D.commonCoefficientField ⊗[ℚ] (D.component i).subspace) :
    D.coefficientDirectSumEquiv
      (DirectSum.lof D.commonCoefficientField _
        (fun i => D.commonCoefficientField ⊗[ℚ] (D.component i).subspace) i x) =
      (D.component i).subspace.subtype.baseChange D.commonCoefficientField x := by
  induction x using TensorProduct.inductionOn with
  | tmul z u => simp
  | add x y hx hy => simp [hx, hy]

/-- A component's normalized basis over the common field. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.componentCoefficientEmbeddingBasis (i : Fin D.numberOfComponents) :
    Module.Basis ((D.component i).field →ₐ[ℚ] ℂ) D.commonCoefficientField
      (D.commonCoefficientField ⊗[ℚ] (D.component i).subspace) :=
  (D.component i).cm.coefficientEmbeddingBasis D.commonCoefficientField
    (D.fieldRange_le_commonCoefficientField i)

/-- The full embedding basis with coefficients in a single finite Galois CM field. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.coefficientEmbeddingBasis : Module.Basis D.EmbeddingIndex D.commonCoefficientField
    (D.commonCoefficientField ⊗[ℚ] U) :=
  (DFinsupp.basis D.componentCoefficientEmbeddingBasis).map D.coefficientDirectSumEquiv

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.coefficientEmbeddingBasis_apply (i : Fin D.numberOfComponents)
    (σ : (D.component i).field →ₐ[ℚ] ℂ) :
    D.coefficientEmbeddingBasis ⟨i, σ⟩ =
      (D.component i).subspace.subtype.baseChange D.commonCoefficientField
        (D.componentCoefficientEmbeddingBasis i σ) := by
  have hb : (DFinsupp.basis D.componentCoefficientEmbeddingBasis) ⟨i, σ⟩ =
      DirectSum.lof D.commonCoefficientField _
        (fun i => D.commonCoefficientField ⊗[ℚ] (D.component i).subspace) i
          (D.componentCoefficientEmbeddingBasis i σ) := by
    simp [DFinsupp.basis, DFinsupp.mapRange.linearEquiv]
    change DFinsupp.mapRange (fun k => (D.componentCoefficientEmbeddingBasis k).repr.symm)
      (fun k => map_zero _) (DFinsupp.single i (Finsupp.single σ 1)) = _
    rw [DFinsupp.mapRange_single, Module.Basis.repr_symm_single, one_smul]
    rfl
  change D.coefficientDirectSumEquiv
    ((DFinsupp.basis D.componentCoefficientEmbeddingBasis) ⟨i, σ⟩) = _
  rw [hb]
  exact D.coefficientDirectSumEquiv_lof i _

/-- Including the coefficients gives exactly the complex basis with its actual Hodge signs. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.coefficientInclusion_embeddingBasis (j : D.EmbeddingIndex) :
    EmbeddingCoefficientField.CM.coefficientInclusion D.commonCoefficientField U (D.coefficientEmbeddingBasis j) =
      D.embeddingBasis j := by
  rcases j with ⟨i, σ⟩
  rw [D.coefficientEmbeddingBasis_apply, EmbeddingCoefficientField.CM.coefficientInclusion_baseChange, D.embeddingBasis_apply]
  congr 1
  exact (D.component i).cm.coefficientInclusion_embeddingBasis D.commonCoefficientField
    (D.fieldRange_le_commonCoefficientField i) σ

/-- Actual scalar conjugation permutes the full normalized basis. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.scalarConjugate_coefficientEmbeddingBasis (g : Gal(D.commonCoefficientField/ℚ))
    (j : D.EmbeddingIndex) :
    ScalarDescent.CM.scalarConjugate ℚ D.commonCoefficientField U g (D.coefficientEmbeddingBasis j) =
      D.coefficientEmbeddingBasis (D.galoisIndex g j) := by
  rcases j with ⟨i, σ⟩
  rw [D.coefficientEmbeddingBasis_apply, EmbeddingCoefficientField.CM.scalarConjugate_baseChange]
  change (D.component i).subspace.subtype.baseChange D.commonCoefficientField
      (ScalarDescent.CM.scalarConjugate ℚ D.commonCoefficientField (D.component i).subspace g
        ((D.component i).cm.coefficientEmbeddingBasis D.commonCoefficientField
          (D.fieldRange_le_commonCoefficientField i) σ)) = _
  rw [(D.component i).cm.scalarConjugate_coefficientEmbeddingBasis]
  exact (D.coefficientEmbeddingBasis_apply i (D.galoisEmbedding g i σ)).symm

/-- The index action is a permutation, with inverse given by the inverse automorphism. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.galoisIndexEquiv (g : Gal(D.commonCoefficientField/ℚ)) : D.EmbeddingIndex ≃ D.EmbeddingIndex where
  toFun := D.galoisIndex g
  invFun := D.galoisIndex g⁻¹
  left_inv j := by rw [← Decomposition.CM.CMDecomposition.galoisIndex_mul, inv_mul_cancel, Decomposition.CM.CMDecomposition.galoisIndex_one]
  right_inv j := by rw [← Decomposition.CM.CMDecomposition.galoisIndex_mul, mul_inv_cancel, Decomposition.CM.CMDecomposition.galoisIndex_one]

/-- The index permutations form an action of the full common Galois group. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.galoisIndexAction : Gal(D.commonCoefficientField/ℚ) →* Equiv.Perm D.EmbeddingIndex where
  toFun := D.galoisIndexEquiv
  map_one' := Equiv.ext D.galoisIndex_one
  map_mul' g h := Equiv.ext (D.galoisIndex_mul g h)

/-- Conjugation transports each coefficient to the correspondingly permuted basis position. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.coefficientEmbeddingBasis_repr_scalarConjugate (g : Gal(D.commonCoefficientField/ℚ))
    (x : D.commonCoefficientField ⊗[ℚ] U) (j : D.EmbeddingIndex) :
    D.coefficientEmbeddingBasis.repr (ScalarDescent.CM.scalarConjugate ℚ D.commonCoefficientField U g x)
        (D.galoisIndex g j) = g (D.coefficientEmbeddingBasis.repr x j) := by
  have hs : ScalarDescent.CM.scalarConjugate ℚ D.commonCoefficientField U g x =
      ∑ i, g (D.coefficientEmbeddingBasis.repr x i) •
        D.coefficientEmbeddingBasis (D.galoisIndex g i) := by
    conv_lhs => rw [← D.coefficientEmbeddingBasis.sum_repr x]
    simp only [map_sum, ScalarDescent.CM.scalarConjugate_smul, D.scalarConjugate_coefficientEmbeddingBasis]
  have hinj : Function.Injective (D.galoisIndex g) := (D.galoisIndexEquiv g).injective
  rw [hs]
  simp [Finsupp.single_apply, hinj.eq_iff]

/-- A rational vector's embedding coefficients transform by the field automorphism. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.rational_embedding_coefficient_galois (g : Gal(D.commonCoefficientField/ℚ))
    (u : U) (j : D.EmbeddingIndex) :
    D.coefficientEmbeddingBasis.repr ((1 : D.commonCoefficientField) ⊗ₜ[ℚ] u)
        (D.galoisIndex g j) =
      g (D.coefficientEmbeddingBasis.repr ((1 : D.commonCoefficientField) ⊗ₜ[ℚ] u) j) := by
  simpa using D.coefficientEmbeddingBasis_repr_scalarConjugate g
    ((1 : D.commonCoefficientField) ⊗ₜ[ℚ] u) j

/-- The support of a rational vector's embedding expansion is stable along full Galois orbits. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.rational_embedding_coefficient_ne_zero_iff (g : Gal(D.commonCoefficientField/ℚ))
    (u : U) (j : D.EmbeddingIndex) :
    D.coefficientEmbeddingBasis.repr ((1 : D.commonCoefficientField) ⊗ₜ[ℚ] u)
        (D.galoisIndex g j) ≠ 0 ↔
      D.coefficientEmbeddingBasis.repr ((1 : D.commonCoefficientField) ⊗ₜ[ℚ] u) j ≠ 0 := by
  rw [D.rational_embedding_coefficient_galois]
  exact map_ne_zero_iff g g.injective

end

end OAI.AlgebraicGeometry.ComplexMultiplication.GaloisEmbeddingBasis.CM.CMDecomposition
