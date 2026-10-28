import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.Incidence
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.KernelBaseChange
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Generated Images -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.GeneratedImages

noncomputable section

/-! Explicit matrices for sums of generated relation modules and a chosen quotient section. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian

universe u v

variable {R : Type u} [CommRing R]
variable {μ ν κ α : Type v} [Fintype ν] [Fintype κ] [Fintype α]
variable [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

theorem matrix_fromCols_range (A : Matrix μ ν R) (B : Matrix μ κ R) :
    (Matrix.toLin' (Matrix.fromCols A B)).range = (Matrix.toLin' A).range ⊔ (Matrix.toLin' B).range := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    change (Matrix.fromCols A B).mulVec v ∈ _
    rw [Matrix.fromCols_mulVec]
    exact Submodule.mem_sup.mpr ⟨A.mulVec (v ∘ Sum.inl), ⟨v ∘ Sum.inl, rfl⟩,
      B.mulVec (v ∘ Sum.inr), ⟨v ∘ Sum.inr, rfl⟩, rfl⟩
  · apply sup_le
    · rintro _ ⟨v, rfl⟩
      refine ⟨Sum.elim v 0, ?_⟩
      change (Matrix.fromCols A B).mulVec (Sum.elim v 0) = A.mulVec v
      rw [Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_zero, add_zero]
    · rintro _ ⟨v, rfl⟩
      refine ⟨Sum.elim 0 v, ?_⟩
      change (Matrix.fromCols A B).mulVec (Sum.elim 0 v) = B.mulVec v
      rw [Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_zero, zero_add]

def matrixColumnFamily (F : α → Matrix μ ν R) : Matrix μ (α × ν) R :=
  fun j p => F p.1 j p.2

theorem matrixColumnFamily_range (F : α → Matrix μ ν R) :
    (Matrix.toLin' (matrixColumnFamily F)).range = ⨆ i, (Matrix.toLin' (F i)).range := by
  have hr : Set.range (matrixColumnFamily F).col = ⋃ i, Set.range (F i).col := by
    ext x
    constructor
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, ⟨j, rfl⟩⟩
    · intro hx
      obtain ⟨i, j, rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i, j⟩, rfl⟩
  rw [Matrix.range_toLin', hr, Submodule.span_iUnion]
  exact congrArg iSup (funext (fun i => (Matrix.range_toLin' (F i)).symm))

variable {ι : Type v} [Fintype ι] [DecidableEq ι] [DecidableEq μ]

def normalizedGenerationMatrix (a : ι → ν) (b : κ → μ)
    (Q : Matrix ι ν R) (F : α → Matrix μ ν R) : Matrix μ ((α × ν) ⊕ κ) R :=
  Matrix.fromCols (matrixColumnFamily (fun i => F i * HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernelMatrix a Q))
    ((1 : Matrix μ μ R).submatrix id b)

theorem normalizedGenerationMatrix_range (a : ι → ν) (b : κ → μ)
    (Q : Matrix ι ν R) (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q) (F : α → Matrix μ ν R) :
    (Matrix.toLin' (normalizedGenerationMatrix a b Q F)).range =
      (⨆ i, ((Matrix.toLin' Q).ker).map (Matrix.toLin' (F i))) ⊔ (HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.selectedBasisMap b).range := by
  rw [normalizedGenerationMatrix, matrix_fromCols_range, matrixColumnFamily_range]
  apply congrArg (fun N => N ⊔ (HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.selectedBasisMap b).range)
  apply congrArg iSup
  funext i
  rw [Matrix.toLin'_mul, LinearMap.range_comp, HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernelMatrix_range a Q hQ]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.GeneratedImages
