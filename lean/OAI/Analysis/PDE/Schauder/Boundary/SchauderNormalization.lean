import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Normalization
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Elliptic normalization that preserves a prescribed flat boundary.  The
positive square root is followed by an orthogonal reflection, so neither
ellipticity nor the quantitative operator bounds are lost. -/

noncomputable section
open InnerProductSpace Matrix
open scoped RealInnerProductSpace

namespace OAI.Analysis.PDE.Schauder

theorem linearEllipticMatrix_eq_inner_adjoint {m : ℕ}
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) (i j : Fin m) :
    linearEllipticMatrix L i j =
      ⟪L.adjoint (EuclideanSpace.single i 1), L.adjoint (EuclideanSpace.single j 1)⟫ := by
  have he (i k : Fin m) : L.adjoint (EuclideanSpace.single i 1) k =
      L (EuclideanSpace.single k 1) i := by
    simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using
      L.adjoint_inner_left (EuclideanSpace.single k 1) (EuclideanSpace.single i 1)
  simp [linearEllipticMatrix, PiLp.inner_apply, he, mul_comm]

theorem linearEllipticMatrix_comp_isometry {m : ℕ}
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (Q : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :
    linearEllipticMatrix (L.comp (Q : _ →L[ℝ] _)) = linearEllipticMatrix L := by
  ext i j
  rw [linearEllipticMatrix_eq_inner_adjoint, linearEllipticMatrix_eq_inner_adjoint,
    ContinuousLinearMap.adjoint_comp, Q.adjoint_eq_symm]
  exact Q.symm.inner_map_map _ _

/-- An invertible map can be postcomposed with an isometry so that its normal
row is a positive multiple of the prescribed unit normal. -/
theorem exists_normal_row_isometry {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (L : E ≃L[ℝ] E) (e : E) (he : ‖e‖ = 1) :
    ∃ (Q : E ≃ₗᵢ[ℝ] E) (c : ℝ), 0 < c ∧
      (∀ x, ⟪e, L (Q x)⟫ = c * ⟪e, x⟫) := by
  let w := L.toContinuousLinearMap.adjoint e
  have hw : w ≠ 0 := by
    intro hzero
    have h := L.toContinuousLinearMap.adjoint_inner_left (L.symm e) e
    change ⟪w, L.symm e⟫ = ⟪e, L (L.symm e)⟫ at h
    simp [hzero, he] at h
  have hc : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let v := ‖w‖⁻¹ • w
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, hc.ne']
  let Q := Submodule.reflection (ℝ ∙ (e - v))ᗮ
  have hQ : Q e = v := Submodule.reflection_sub (he.trans hv.symm)
  have hscale : w = ‖w‖ • Q e := by
    rw [hQ]
    simp [v, smul_smul, hc.ne']
  refine ⟨Q, ‖w‖, hc, ?_⟩
  intro x
  calc
    ⟪e, L (Q x)⟫ = ⟪w, Q x⟫ :=
      (L.toContinuousLinearMap.adjoint_inner_left (Q x) e).symm
    _ = ‖w‖ * ⟪Q e, Q x⟫ := by
      conv_lhs => rw [hscale, real_inner_smul_left]
    _ = ‖w‖ * ⟪e, x⟫ := by rw [Q.inner_map_map]

/-- A positive definite matrix has a square-root normalization preserving the
chosen positive halfspace and its boundary, with the usual ellipticity bounds. -/
theorem exists_boundary_elliptic_normalization_bounded {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef) (k : Fin m)
    {ell Λ : ℝ} (hell : 0 < ell) (hΛ : 0 ≤ Λ)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin m), ell * ‖x‖ ^ 2 ≤
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫)
    (hupper : ∀ x : EuclideanSpace ℝ (Fin m),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫ ≤ Λ * ‖x‖ ^ 2) :
    ∃ (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) (c : ℝ),
      0 < c ∧ linearEllipticMatrix L.toContinuousLinearMap = A ∧
      (∀ x, L x k = c * x k) ∧
      ‖L.toContinuousLinearMap‖ ≤ Real.sqrt Λ ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt ell)⁻¹ := by
  obtain ⟨L₀, hL₀, hnorm, hinv⟩ :=
    exists_elliptic_normalization_bounded A hA hell hΛ hlower hupper
  obtain ⟨Q, c, hc, hQ⟩ := exists_normal_row_isometry L₀
    (EuclideanSpace.single k 1) (by simp)
  let L := Q.toContinuousLinearEquiv.trans L₀
  have hL : L.toContinuousLinearMap = L₀.toContinuousLinearMap.comp (Q : _ →L[ℝ] _) := rfl
  refine ⟨L, c, hc, ?_, ?_, ?_, ?_⟩
  · rw [hL, linearEllipticMatrix_comp_isometry, hL₀]
  · intro x
    simpa [L, EuclideanSpace.inner_single_left] using hQ x
  · apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg Λ)
    intro x
    change ‖L₀ (Q x)‖ ≤ _
    calc
      _ ≤ ‖L₀.toContinuousLinearMap‖ * ‖Q x‖ := L₀.toContinuousLinearMap.le_opNorm _
      _ ≤ Real.sqrt Λ * ‖x‖ := by rw [Q.norm_map]; gcongr
  · apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg ell))
    intro x
    change ‖Q.symm (L₀.symm x)‖ ≤ _
    rw [Q.symm.norm_map]
    exact (L₀.symm.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hinv (norm_nonneg x))

end OAI.Analysis.PDE.Schauder
