import OAI.LinearAlgebra.Moore.Monotone

/-! The determinant-square identity on the positive quaternionic cone. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix Set
open scoped MatrixOrder ComplexOrder

theorem hasDerivAt_complexDet_invertible {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℝ → Matrix I I ℂ) (N : Matrix I I ℂ) (t : ℝ)
    (hdet : (M t).det ≠ 0)
    (h : ∀ i j, HasDerivAt (fun s ↦ M s i j) (N i j) t) :
    HasDerivAt (fun s ↦ (M s).det) ((M t).det * ((M t)⁻¹ * N).trace) t := by
  let F : ℝ → Matrix I I ℂ := fun s ↦ (M t)⁻¹ * M s
  have hF : F t = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have hdF (i j : I) : HasDerivAt (fun s ↦ F s i j) (((M t)⁻¹ * N) i j) t := by
    simpa only [F, Matrix.mul_apply] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦ (h k j).const_mul ((M t)⁻¹ i k))
  have hd := (hasDerivAt_complexDet_identity F _ t hF hdF).const_mul (M t).det
  have he (s : ℝ) : (M t).det * (F s).det = (M s).det := by
    rw [← Matrix.det_mul]
    simp only [F, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mul]
  simpa only [he] using hd

/-- A direct differential proof, starting at the identity, fixes the sign of
the Moore determinant and identifies its square with the complex determinant. -/
theorem mooreDet_sq_eq_complexify_det_of_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : (complexify A).PosDef) :
    mooreDet n A ^ 2 = (complexify A).det.re := by
  let D := A - 1
  let B : ℝ → Matrix (Fin n) (Fin n) (Quaternion ℝ) := fun t ↦ 1 + t • D
  have hD : D.IsHermitian := (isHermitian_of_complexify hA.isHermitian).sub isHermitian_one
  have hBform (t : ℝ) : complexify (B t) =
      (1 - t) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) + t • complexify A := by
    simp only [B, D, complexify_add, complexify_real_smul, complexify_sub, complexify_one,
      smul_sub, sub_smul, one_smul]
    abel
  have hBpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (complexify (B t)).PosDef := by
    rw [hBform]
    exact complex_posDef_segment_identity hA ht
  let f : ℝ → ℝ := fun t ↦ mooreDet n (B t) ^ 2 / (complexify (B t)).det.re
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f 0 t := by
    have hm : HasDerivAt (fun s ↦ mooreDet n (B s))
        (mooreDet n (B t) * (((complexify (B t))⁻¹ * complexify D).trace.re / 2)) t := by
      convert! hasDerivAt_mooreDet_affine 1 D t using 1
      exact (mooreDifferential_eq_complex_inverse (B t) D (hBpos t ht) hD).symm
    have he (i j : Fin n × Fin 2) :
        HasDerivAt (fun s ↦ complexify (B s) i j) (complexify D i j) t := by
      simp only [B, complexify_add, complexify_real_smul, Matrix.add_apply, Matrix.smul_apply]
      convert! (hasDerivAt_const t (complexify (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) i j)).add
        ((hasDerivAt_id t).smul_const (complexify D i j)) using 1
      simp
    have hc := hasDerivAt_complexDet_invertible (fun s ↦ complexify (B s))
      (complexify D) t (hBpos t ht).det_pos.ne' he
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hc
    change HasDerivAt (fun s ↦ (complexify (B s)).det.re)
      ((complexify (B t)).det * ((complexify (B t))⁻¹ * complexify D).trace).re t at hr
    rw [Complex.mul_re, complexify_det_real, zero_mul, sub_zero] at hr
    have hden : (complexify (B t)).det.re ≠ 0 := (hBpos t ht).det_pos.1.ne'
    change HasDerivAt (fun s ↦ mooreDet n (B s) ^ 2 / (complexify (B s)).det.re) 0 t
    convert! (hm.pow 2).div hr hden using 1
    simp only [Pi.pow_apply]
    field_simp
    ; ring
  have hnorm := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (x := 0) (y := 1)
    (fun t ht ↦ (hf t ht).hasDerivWithinAt)
    (C := 0) (fun _ _ ↦ by simp) (by simp) (by simp)
  have h10 : f 1 = f 0 := sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm (by simpa using hnorm) (norm_nonneg _)))
  have hratio : mooreDet n A ^ 2 / (complexify A).det.re = 1 := by
    simpa [f, B, D, mooreDet_identity, complexify_one] using h10
  exact (div_eq_one_iff_eq (hA.det_pos.1.ne')).mp hratio

end OAI.LinearAlgebra.Moore
