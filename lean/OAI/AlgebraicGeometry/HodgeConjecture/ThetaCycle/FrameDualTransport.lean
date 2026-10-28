import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicFrameDeterminant

/-! # Frame Dual Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FrameDualTransport.CM

noncomputable section

/-! Dual coordinate transport through a factored frame denominator,
including arbitrary finite reindexing. -/

open scoped Classical _root_.Matrix

theorem frame_inverse_transpose_cancel {I : Type} [Fintype I] [DecidableEq I]
    (J₀ J F C G : Matrix I I ℂ) (h : J₀ * J = F * C * G)
    (hG : IsUnit G.det) (u : I → ℂ) :
    J₀⁻¹ᵀ.mulVec (J⁻¹ᵀ.mulVec (Gᵀ.mulVec u)) = F⁻¹ᵀ.mulVec (C⁻¹ᵀ.mulVec u) := by
  have ht := congrArg (fun M : Matrix I I ℂ => M⁻¹ᵀ) h
  simp only [Matrix.mul_inv_rev, Matrix.transpose_mul] at ht
  rw [Matrix.mulVec_mulVec, ht, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    ← Matrix.transpose_mul G G⁻¹, Matrix.mul_nonsing_inv G hG, Matrix.transpose_one,
    mul_one, ← Matrix.mulVec_mulVec]

theorem reindexed_inverse_transpose_mulVec {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (M : Matrix J J ℂ) (u : I → ℂ) :
    (fun j => ((M.submatrix e e)⁻¹ᵀ).mulVec u (e.symm j)) =
      M⁻¹ᵀ.mulVec (fun j => u (e.symm j)) := by
  rw [Matrix.inv_submatrix_equiv]
  have h := SourceIntrinsicFrameDeterminant.CM.same_index_matrix_mulVec e M⁻¹ᵀ (fun j => u (e.symm j))
  simp only [Equiv.symm_apply_apply] at h
  funext j
  exact (congrFun h (e.symm j)).trans (congrArg (M⁻¹ᵀ.mulVec (fun j => u (e.symm j)))
    (e.apply_symm_apply j))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FrameDualTransport.CM
