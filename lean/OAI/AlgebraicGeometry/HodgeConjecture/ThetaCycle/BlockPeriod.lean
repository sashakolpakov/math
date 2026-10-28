import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus
import OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix

/-! # Block Period -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BlockPeriod.CM

noncomputable section

/-! The actual block-diagonal Siegel period of the original two lines. -/

open scoped Classical _root_.Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem real_block_positive (A : Matrix ι ι ℝ) (D : Matrix κ κ ℝ)
    (hA : A.PosDef) (hD : D.PosDef) : (Matrix.fromBlocks A 0 0 D).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.isHermitian_iff_isSymm.mpr
      ((Matrix.isHermitian_iff_isSymm.mp hA.1).fromBlocks (by simp)
        (Matrix.isHermitian_iff_isSymm.mp hD.1))
  · intro v hv
    let u₀ : ι → ℝ := fun i => v (Sum.inl i)
    let u₁ : κ → ℝ := fun i => v (Sum.inr i)
    have hne : u₀ ≠ 0 ∨ u₁ ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hv
      funext i
      cases i with
      | inl j => exact congrFun hn.1 j
      | inr j => exact congrFun hn.2 j
    have hs : v ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ v) =
        u₀ ⬝ᵥ (A *ᵥ u₀) + u₁ ⬝ᵥ (D *ᵥ u₁) := by
      simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, u₀, u₁]
    simp only [star_trivial]
    rw [hs]
    have h₀ := hA.posSemidef.dotProduct_mulVec_nonneg u₀
    have h₁ := hD.posSemidef.dotProduct_mulVec_nonneg u₁
    rcases hne with hne | hne
    · have hp := hA.dotProduct_mulVec_pos hne
      simpa only [star_trivial] using add_pos_of_pos_of_nonneg hp h₁
    · have hp := hD.dotProduct_mulVec_pos hne
      simpa only [star_trivial] using add_pos_of_nonneg_of_pos h₀ hp

def blockPeriod (Z₀ : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Z₁ : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix κ) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Sum ι κ) where
  matrix := Matrix.fromBlocks Z₀.matrix 0 0 Z₁.matrix
  symmetric := Z₀.symmetric.fromBlocks (by simp) Z₁.symmetric
  imaginary_posDef := by
    have hm : (fun i j => (Matrix.fromBlocks Z₀.matrix 0 0 Z₁.matrix i j).im) =
        Matrix.fromBlocks (fun i j => (Z₀.matrix i j).im) 0 0
          (fun i j => (Z₁.matrix i j).im) := by
      funext i j
      cases i <;> cases j <;> rfl
    rw [hm]
    exact real_block_positive _ _ Z₀.imaginary_posDef Z₁.imaginary_posDef

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BlockPeriod.CM
