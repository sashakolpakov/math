import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReindexedTheta
import OAI.RepresentationTheory.Hecke.RadialDilation.SiegelFrame

/-! # Reindexed Frame Gradient -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReindexedFrameGradient.TestTransport

noncomputable section

/-! The first coefficient in two frames related by a reindexing and a
diagonal column scaling. The formula uses the actual matrix inverses. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable (e : I ≃ J)

omit [Fintype I] [Fintype J] in
theorem gradientVector_reindexed (l : (I → ℂ) →L[ℂ] ℂ) (i : I) :
    RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector (l.comp (ReindexedTheta.TestTransport.positionReindexLinear e ℂ)) (e i) = RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector l i := by
  change l (ReindexedTheta.TestTransport.positionReindexLinear e ℂ (Pi.single (e i) 1)) = l (Pi.single i 1)
  congr 1
  funext j
  change (Pi.single (e i) (1 : ℂ) : J → ℂ) (e j) =
    (Pi.single i (1 : ℂ) : I → ℂ) j
  simp only [Pi.single_apply, e.injective.eq_iff]

theorem inverse_frame_reindexed (M : (Matrix J J ℂ)ˣ) (c : I → ℂ)
    (L : Matrix I I ℂ) (hL : M.val.submatrix e e * Matrix.diagonal c = L)
    (hdet : L.det ≠ 0) :
    M.inv.submatrix e e = Matrix.diagonal c * L⁻¹ := by
  have hmul : M.inv.submatrix e e * L = Matrix.diagonal c := by
    rw [← hL, ← Matrix.mul_assoc, Matrix.submatrix_mul_equiv, M.inv_val]
    simp only [Matrix.submatrix_one_equiv, Matrix.one_mul]
  calc
    M.inv.submatrix e e = M.inv.submatrix e e * (L * L⁻¹) := by
      rw [Matrix.mul_nonsing_inv L (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one]
    _ = (M.inv.submatrix e e * L) * L⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = Matrix.diagonal c * L⁻¹ := by rw [hmul]

theorem frameGradient_reindexed_scaled (M : (Matrix J J ℂ)ˣ) (c : I → ℂ)
    (L : Matrix I I ℂ) (hL : M.val.submatrix e e * Matrix.diagonal c = L)
    (hdet : L.det ≠ 0) (l : (I → ℂ) →L[ℂ] ℂ) (i : I) :
    (M.inv *ᵥ RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector (l.comp (ReindexedTheta.TestTransport.positionReindexLinear e ℂ))) (e i) =
      c i * RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.frameGradient L l i := by
  have hreindex : (M.inv *ᵥ RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector (l.comp (ReindexedTheta.TestTransport.positionReindexLinear e ℂ))) (e i) =
      (M.inv.submatrix e e *ᵥ RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector l) i := by
    change (∑ j : J, M.inv (e i) j *
      RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector (l.comp (ReindexedTheta.TestTransport.positionReindexLinear e ℂ)) j) =
      ∑ j : I, M.inv (e i) (e j) * RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector l j
    rw [← e.sum_comp (fun j : J => M.inv (e i) j *
      RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector (l.comp (ReindexedTheta.TestTransport.positionReindexLinear e ℂ)) j)]
    simp only [gradientVector_reindexed]
  rw [hreindex, inverse_frame_reindexed e M c L hL hdet, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_diagonal]
  rfl

theorem frameCovector_reindexed_scaled (M : (Matrix J J ℂ)ˣ) (c : I → ℂ)
    (L : Matrix I I ℂ) (hL : M.val.submatrix e e * Matrix.diagonal c = L)
    (hdet : L.det ≠ 0) (l : (I → ℂ) →L[ℂ] ℂ) (i : I) :
    (l.comp (ReindexedTheta.TestTransport.positionReindexLinear e ℂ)) (M.invᵀ *ᵥ Pi.single (e i) 1) =
      c i * RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.frameGradient L l i := by
  have h := congrFun (RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradient_precompose (l.comp (ReindexedTheta.TestTransport.positionReindexLinear e ℂ)) M.invᵀ) (e i)
  rw [Matrix.transpose_transpose] at h
  exact h.trans (frameGradient_reindexed_scaled e M c L hL hdet l i)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReindexedFrameGradient.TestTransport
