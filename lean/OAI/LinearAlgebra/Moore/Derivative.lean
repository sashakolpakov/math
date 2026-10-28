import OAI.LinearAlgebra.Moore.Rank.One

/-! The full first variation of the signed Moore determinant. -/

namespace OAI.LinearAlgebra.Moore

open Matrix

/-- Explicit differential of the Pfaffian polynomial. -/
noncomputable def pfaffianDifferential (n : ℕ)
    (M N : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) : ℂ :=
  (2 ^ n * (n.factorial : ℂ))⁻¹ *
    ∑ σ : Equiv.Perm (Fin n × Fin 2), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, M (σ (j, 0)) (σ (j, 1))) *
        N (σ (i, 0)) (σ (i, 1))

/-- The polynomial differential differentiates every entrywise differentiable
matrix path; the path parameter is real but the entries may be complex. -/
theorem hasDerivAt_pfaffian_path (n : ℕ)
    (M : ℝ → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ)
    (N : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) (t : ℝ)
    (h : ∀ i j, HasDerivAt (fun s => M s i j) (N i j) t) :
    HasDerivAt (fun s => pfaffian n (M s)) (pfaffianDifferential n (M t) N) t := by
  unfold pfaffian pfaffianDifferential
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro σ _
  apply HasDerivAt.const_mul
  simpa only [smul_eq_mul] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ)
      (fun i _ => h (σ (i, 0)) (σ (i, 1))))

theorem pfaffianDifferential_add (n : ℕ)
    (M N P : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    pfaffianDifferential n M (N + P) =
      pfaffianDifferential n M N + pfaffianDifferential n M P := by
  simp [pfaffianDifferential, mul_add, Finset.sum_add_distrib]

theorem pfaffianDifferential_smul (n : ℕ) (c : ℂ)
    (M N : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    pfaffianDifferential n M (c • N) = c * pfaffianDifferential n M N := by
  have hg (a : ℂ) (f g : Fin n → ℂ) :
      a * (∑ i, f i * (c * g i)) = c * (a * ∑ i, f i * g i) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [pfaffianDifferential, Matrix.smul_apply, smul_eq_mul]
  rw [mul_left_comm c]
  congr 1
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact hg _ _ _

/-- Euler's identity for the homogeneous degree-`n` Pfaffian polynomial. -/
theorem pfaffianDifferential_self (n : ℕ)
    (M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    pfaffianDifferential n M M = (n : ℂ) * pfaffian n M := by
  have hp (σ : Equiv.Perm (Fin n × Fin 2)) (i : Fin n) :
      (∏ j ∈ Finset.univ.erase i, M (σ (j, 0)) (σ (j, 1))) * M (σ (i, 0)) (σ (i, 1)) =
      ∏ j : Fin n, M (σ (j, 0)) (σ (j, 1)) :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  simp only [pfaffianDifferential, hp, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, pfaffian]
  simp_rw [mul_left_comm _ (n : ℂ), ← Finset.mul_sum]
  ring

/-- Each scalar entry of the quaternion-to-skew representation is real-linear. -/
def skewQuaternionEntryLinear (a b : Fin 2) : Quaternion ℝ →ₗ[ℝ] ℂ where
  toFun q := skewQuaternion q a b
  map_add' p q := by
    unfold skewQuaternion
    rw [quaternionMatrix_add, Matrix.add_mul]
    rfl
  map_smul' s q := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M a b) (skewQuaternion_smul s q)
    simpa only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, RingHom.id_apply] using h

noncomputable def skewQuaternionEntryCLM (a b : Fin 2) : Quaternion ℝ →L[ℝ] ℂ :=
  (skewQuaternionEntryLinear a b).toContinuousLinearMap

/-- Real differential of the signed Moore determinant. -/
noncomputable def mooreDifferential (n : ℕ)
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) : ℝ :=
  (pfaffianDifferential n (skewComplexify A) (skewComplexify D)).re

/-- Full quaternionic first variation along every entrywise differentiable path. -/
theorem hasDerivAt_mooreDet_path (n : ℕ)
    (A : ℝ → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (t : ℝ)
    (h : ∀ i j, HasDerivAt (fun s => A s i j) (D i j) t) :
    HasDerivAt (fun s => mooreDet n (A s)) (mooreDifferential n (A t) D) t := by
  have hsk : ∀ i j : Fin n × Fin 2,
      HasDerivAt (fun s => skewComplexify (A s) i j) (skewComplexify D i j) t := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    exact (skewQuaternionEntryCLM a b).hasFDerivAt.comp_hasDerivAt t (h i j)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_pfaffian_path n (fun s => skewComplexify (A s)) (skewComplexify D) t hsk)

theorem mooreDifferential_add (n : ℕ)
    (A D E : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    mooreDifferential n A (D + E) = mooreDifferential n A D + mooreDifferential n A E := by
  simp only [mooreDifferential, skewComplexify_add, pfaffianDifferential_add, Complex.add_re]

theorem mooreDifferential_smul (n : ℕ) (c : ℝ)
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    mooreDifferential n A (c • D) = c * mooreDifferential n A D := by
  simp only [mooreDifferential, skewComplexify_real_smul, pfaffianDifferential_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Euler contraction identity for the signed Moore determinant. -/
theorem mooreDifferential_self (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    mooreDifferential n A A = (n : ℝ) * mooreDet n A := by
  rw [mooreDifferential, pfaffianDifferential_self, mooreDet]
  simp

end OAI.LinearAlgebra.Moore
