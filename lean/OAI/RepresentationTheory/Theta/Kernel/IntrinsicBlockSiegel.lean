import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # Intrinsic Block Siegel -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSiegel.Intrinsic

noncomputable section

/-! Actual block Siegel matrices and determinant frames. The period
positivity and determinant products are proved, not postulated. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
theorem positive_blocks {A : Matrix I I ℝ} {B : Matrix J J ℝ}
    (hA : A.PosDef) (hB : B.PosDef) : (Matrix.fromBlocks A 0 0 B).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hA.1.fromBlocks (by simp) hB.1)
  intro x hx
  let x₁ : I → ℝ := fun i => x (.inl i)
  let x₂ : J → ℝ := fun j => x (.inr j)
  have he : star x ⬝ᵥ ((Matrix.fromBlocks A 0 0 B).mulVec x) =
      star x₁ ⬝ᵥ (A.mulVec x₁) + star x₂ ⬝ᵥ (B.mulVec x₂) := by
    simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks, x₁, x₂]
  rw [he]
  by_cases h₁ : x₁ = 0
  · have h₂ : x₂ ≠ 0 := by
      intro h₂
      apply hx
      funext i
      rcases i with i | i
      · exact congrFun h₁ i
      · exact congrFun h₂ i
    have hpos := hB.dotProduct_mulVec_pos h₂
    simpa [h₁] using hpos
  · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos h₁)
      (hB.posSemidef.dotProduct_mulVec_nonneg x₂)

def blockPeriod (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J) : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (I ⊕ J) where
  matrix := Matrix.fromBlocks Z₁.matrix 0 0 Z₂.matrix
  symmetric := by
    unfold Matrix.IsSymm
    simp only [Matrix.fromBlocks_transpose, Z₁.symmetric.eq, Z₂.symmetric.eq, Matrix.transpose_zero]
  imaginary_posDef := by
    have he : (fun i j => (Matrix.fromBlocks Z₁.matrix 0 0 Z₂.matrix i j).im) =
        Matrix.fromBlocks (fun i j => (Z₁.matrix i j).im) 0 0
          (fun i j => (Z₂.matrix i j).im) := by
      funext i j
      rcases i with i | i <;> rcases j with j | j <;> rfl
    rw [he]
    exact positive_blocks Z₁.imaginary_posDef Z₂.imaginary_posDef

def blockFrame (a : (Matrix I I ℂ)ˣ) (b : (Matrix J J ℂ)ˣ) :
    (Matrix (I ⊕ J) (I ⊕ J) ℂ)ˣ where
  val := Matrix.fromBlocks a.val 0 0 b.val
  inv := Matrix.fromBlocks a.inv 0 0 b.inv
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

theorem blockFrame_invTranspose_mulVec (a : (Matrix I I ℂ)ˣ) (b : (Matrix J J ℂ)ˣ)
    (u : I → ℂ) (v : J → ℂ) :
    (blockFrame a b).invᵀ.mulVec (Sum.elim u v) =
      Sum.elim (a.invᵀ.mulVec u) (b.invᵀ.mulVec v) := by
  funext q
  rcases q with q | q <;>
    simp [blockFrame, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type]

theorem blockFrame_det (a : (Matrix I I ℂ)ˣ) (b : (Matrix J J ℂ)ˣ) :
    (blockFrame a b).val.det = a.val.det * b.val.det :=
  Matrix.det_fromBlocks_zero₂₁ _ _ _

theorem blockHalfFrame (a : (Matrix I I ℂ)ˣ) (b : (Matrix J J ℂ)ˣ)
    (s t : ℂ) (hs : s ≠ 0 ∧ s ^ 2 = a.val.det) (ht : t ≠ 0 ∧ t ^ 2 = b.val.det) :
    s * t ≠ 0 ∧ (s * t) ^ 2 = (blockFrame a b).val.det := by
  exact ⟨mul_ne_zero hs.1 ht.1, by rw [mul_pow, hs.2, ht.2, blockFrame_det]⟩

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSiegel.Intrinsic
