import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Constant

/-! Positive definite real matrices admit the actual Euclidean linear normalization
used to freeze a uniformly elliptic operator. -/

noncomputable section
open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian Matrix
open scoped MatrixOrder RealInnerProductSpace
namespace OAI.Analysis.PDE.Schauder

theorem toEuclideanCLM_single {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (i j : Fin m) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) A (EuclideanSpace.single j (1 : ℝ)) i = A i j := by
  change (A *ᵥ Pi.single j 1) i = A i j
  simp

theorem linearEllipticMatrix_toEuclideanCLM {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) :
    linearEllipticMatrix (Matrix.toEuclideanCLM (𝕜 := ℝ) A) = A * A.transpose := by
  ext i j
  simp only [linearEllipticMatrix, toEuclideanCLM_single, Matrix.mul_apply, Matrix.transpose_apply]

theorem exists_elliptic_normalization {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef) :
    ∃ L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      linearEllipticMatrix L.toContinuousLinearMap = A ∧
      ∀ x, ‖L x‖ ^ 2 = ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫ := by
  let S := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hSunit : IsUnit S := (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit
  have hunit : IsUnit (Matrix.toEuclideanCLM (𝕜 := ℝ) S) :=
    hSunit.map (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ))
  obtain ⟨U, hU⟩ := hunit
  let L := ContinuousLinearEquiv.unitsEquiv ℝ (EuclideanSpace ℝ (Fin m)) U
  have hL : L.toContinuousLinearMap = Matrix.toEuclideanCLM (𝕜 := ℝ) S := by
    exact hU
  have hsym : S.transpose = S := by
    have he : S.conjTranspose = S := hS.isHermitian
    simpa using he
  have hsq : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  refine ⟨L, ?_, ?_⟩
  · rw [hL, linearEllipticMatrix_toEuclideanCLM, hsym, hsq]
  · intro x
    change ‖L.toContinuousLinearMap x‖ ^ 2 = _
    rw [hL]
    have hadj : (Matrix.toEuclideanCLM (𝕜 := ℝ) S).adjoint = Matrix.toEuclideanCLM (𝕜 := ℝ) S := by
      change star (Matrix.toEuclideanCLM (𝕜 := ℝ) S) = Matrix.toEuclideanCLM (𝕜 := ℝ) S
      rw [← map_star]
      congr 1
    have hcomp : (Matrix.toEuclideanCLM (𝕜 := ℝ) S).adjoint.comp (Matrix.toEuclideanCLM (𝕜 := ℝ) S) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) A := by
      rw [hadj]
      change Matrix.toEuclideanCLM (𝕜 := ℝ) S * Matrix.toEuclideanCLM (𝕜 := ℝ) S = _
      rw [← map_mul, hsq]
    simpa only [hcomp, RCLike.re_to_real] using
      (Matrix.toEuclideanCLM (𝕜 := ℝ) S).apply_norm_sq_eq_inner_adjoint_right x

theorem exists_elliptic_normalization_bounded {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    {ell Λ : ℝ} (hell : 0 < ell) (hΛ : 0 ≤ Λ)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin m), ell * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫)
    (hupper : ∀ x : EuclideanSpace ℝ (Fin m), ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫ ≤ Λ * ‖x‖ ^ 2) :
    ∃ L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      linearEllipticMatrix L.toContinuousLinearMap = A ∧
      ‖L.toContinuousLinearMap‖ ≤ Real.sqrt Λ ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt ell)⁻¹ := by
  obtain ⟨L, hL, henergy⟩ := exists_elliptic_normalization A hA
  refine ⟨L, hL, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg Λ)
    intro x
    have he := (henergy x).trans_le (hupper x)
    have hs := Real.sq_sqrt hΛ
    have hx : ‖L x‖ ≤ Real.sqrt Λ * ‖x‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg Λ) (norm_nonneg _))).mp
      nlinarith
    exact hx
  · apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg ell))
    intro x
    have he := hlower (L.symm x)
    rw [← henergy, L.apply_symm_apply] at he
    have hs := Real.sq_sqrt hell.le
    have hsp : 0 < Real.sqrt ell := Real.sqrt_pos.mpr hell
    have hx : Real.sqrt ell * ‖L.symm x‖ ≤ ‖x‖ := by
      apply (sq_le_sq₀ (mul_nonneg hsp.le (norm_nonneg _)) (norm_nonneg _)).mp
      nlinarith
    change ‖L.symm x‖ ≤ _
    calc
      ‖L.symm x‖ ≤ ‖x‖ / Real.sqrt ell := (le_div_iff₀ hsp).mpr (by nlinarith)
      _ = _ := by ring

theorem compact_posDef_schauder {m : ℕ} (hm : 3 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef) :
    ∃ C > 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
      ∀ F, 0 ≤ F →
      (∀ x y, |nondivergenceOperator (fun _ => A) u x -
        nondivergenceOperator (fun _ => A) u y| ≤ F * ‖x - y‖ ^ α) →
      ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * F * ‖x - y‖ ^ α := by
  obtain ⟨L, hL, _⟩ := exists_elliptic_normalization A hA
  simpa only [hL] using compact_constant_coefficient_schauder hm hα hα1 L

end OAI.Analysis.PDE.Schauder
