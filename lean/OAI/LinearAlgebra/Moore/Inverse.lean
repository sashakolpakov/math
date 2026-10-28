import OAI.LinearAlgebra.Moore.Derivative
import OAI.LinearAlgebra.Moore.Normalize

/-! Infinitesimal congruence and inverse linearization of the Moore determinant. -/

namespace OAI.LinearAlgebra.Moore

open Matrix

noncomputable def complexDetDifferential {I : Type*} [Fintype I] [DecidableEq I]
    (M N : Matrix I I ℂ) : ℂ :=
  ∑ σ : Equiv.Perm I, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
    ∑ i : I, (∏ j ∈ Finset.univ.erase i, M (σ j) j) * N (σ i) i

theorem hasDerivAt_complexDet_path {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℝ → Matrix I I ℂ) (N : Matrix I I ℂ) (t : ℝ)
    (h : ∀ i j, HasDerivAt (fun s => M s i j) (N i j) t) :
    HasDerivAt (fun s => (M s).det) (complexDetDifferential (M t) N) t := by
  simp only [Matrix.det_apply', complexDetDifferential]
  apply HasDerivAt.fun_sum
  intro σ _
  apply HasDerivAt.const_mul
  simpa only [smul_eq_mul] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => h (σ i) i))

theorem complexDetDifferential_one {I : Type*} [Fintype I] [DecidableEq I]
    (N : Matrix I I ℂ) : complexDetDifferential 1 N = N.trace := by
  classical
  have hex (σ : Equiv.Perm I) (hσ : σ ≠ 1) (i : I) :
      ∃ j, j ≠ i ∧ σ j ≠ j := by
    by_contra h
    push Not at h
    apply hσ
    apply Equiv.ext
    intro j
    by_cases hj : j = i
    · subst j
      by_cases hi : σ i = i
      · exact hi
      · exact σ.injective (h (σ i) hi)
    · exact h j hj
  unfold complexDetDifferential
  rw [Finset.sum_eq_single (1 : Equiv.Perm I)]
  · simp [Matrix.trace, Matrix.one_apply]
  · intro σ _ hσ
    apply mul_eq_zero.mpr
    right
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨j, hji, hj⟩ := hex σ hσ i
    have hp : (∏ l ∈ Finset.univ.erase i, (1 : Matrix I I ℂ) (σ l) l) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)
      simp [hj]
    rw [hp, zero_mul]
  · simp

theorem hasDerivAt_complexDet_identity {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℝ → Matrix I I ℂ) (N : Matrix I I ℂ) (t : ℝ) (hM : M t = 1)
    (h : ∀ i j, HasDerivAt (fun s => M s i j) (N i j) t) :
    HasDerivAt (fun s => (M s).det) N.trace t := by
  have hd := hasDerivAt_complexDet_path M N t h
  rw [hM, complexDetDifferential_one] at hd
  exact hd

theorem hasDerivAt_quaternionMatrix_mul {I J K : Type*} [Fintype J]
    (A : ℝ → Matrix I J (Quaternion ℝ)) (B : ℝ → Matrix J K (Quaternion ℝ))
    (D : Matrix I J (Quaternion ℝ)) (E : Matrix J K (Quaternion ℝ)) (t : ℝ)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (D i j) t)
    (hB : ∀ j k, HasDerivAt (fun s => B s j k) (E j k) t) :
    ∀ i k, HasDerivAt (fun s => (A s * B s) i k)
      ((D * B t + A t * E) i k) t := by
  intro i k
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hA i j).mul (hB j k))
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib, Pi.mul_apply] using! h

def quaternionStarLinear : Quaternion ℝ →ₗ[ℝ] Quaternion ℝ where
  toFun := star
  map_add' := star_add
  map_smul' s q := by
    ext <;> simp

noncomputable def quaternionStarCLM : Quaternion ℝ →L[ℝ] Quaternion ℝ :=
  quaternionStarLinear.toContinuousLinearMap

theorem hasDerivAt_quaternionMatrix_star {I J : Type*}
    (A : ℝ → Matrix I J (Quaternion ℝ)) (D : Matrix I J (Quaternion ℝ)) (t : ℝ)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (D i j) t) :
    ∀ j i, HasDerivAt (fun s => (A s)ᴴ j i) (Dᴴ j i) t := by
  intro j i
  exact quaternionStarCLM.hasFDerivAt.comp_hasDerivAt t (hA i j)

theorem quaternionMatrix_real_smul (s : ℝ) (q : Quaternion ℝ) :
    quaternionMatrix (s • q) = s • quaternionMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quaternionMatrix]

theorem complexify_real_smul {I J : Type*} (s : ℝ) (A : Matrix I J (Quaternion ℝ)) :
    complexify (s • A) = s • complexify A := by
  ext ⟨i, a⟩ ⟨j, b⟩
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M a b)
    (quaternionMatrix_real_smul s (A i j))

theorem complexify_trace_real (n : ℕ) (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    (complexify A).trace.re = 2 * ∑ i : Fin n, (A i i).re := by
  simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two, complexify, quaternionMatrix,
    Finset.mul_sum, two_mul]

/-- Differentiate the exact congruence law at the identity. This identity is
valid without positivity or invertibility assumptions. -/
theorem mooreDifferential_congruence (n : ℕ)
    (A E : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    mooreDifferential n A (E * A + A * Eᴴ) =
      (complexify E).trace.re * mooreDet n A := by
  let B : ℝ → Matrix (Fin n) (Fin n) (Quaternion ℝ) := fun s => 1 + s • E
  have hB0 : B 0 = 1 := by simp [B]
  have hB : ∀ i j, HasDerivAt (fun s => B s i j) (E i j) 0 := by
    intro i j
    change HasDerivAt (fun s : ℝ => (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) i j +
      s • E i j) (E i j) 0
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const (E i j)).const_add
      ((1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) i j) using 1
    simp
  have hBA : ∀ i j, HasDerivAt (fun s => (B s * A) i j) ((E * A) i j) 0 := by
    have h := hasDerivAt_quaternionMatrix_mul B (fun _ => A) E 0 0 hB
      (fun i j => hasDerivAt_const 0 (A i j))
    simpa only [hB0, Matrix.mul_zero, add_zero] using h
  have hF : ∀ i j, HasDerivAt (fun s => (B s * A * (B s)ᴴ) i j)
      ((E * A + A * Eᴴ) i j) 0 := by
    have h := hasDerivAt_quaternionMatrix_mul (fun s => B s * A) (fun s => (B s)ᴴ)
      (E * A) Eᴴ 0 hBA (hasDerivAt_quaternionMatrix_star B E 0 hB)
    simpa only [hB0, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul] using h
  have hm := hasDerivAt_mooreDet_path n (fun s => B s * A * (B s)ᴴ) (E * A + A * Eᴴ) 0 hF
  simp only [hB0, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul] at hm
  have hCB (s : ℝ) : complexify (B s) = 1 + s • complexify E := by
    dsimp only [B]
    rw [complexify_add, complexify_one, complexify_real_smul]
  have hC : ∀ i j : Fin n × Fin 2,
      HasDerivAt (fun s => complexify (B s) i j) (complexify E i j) 0 := by
    intro i j
    simp only [hCB]
    change HasDerivAt (fun s : ℝ => (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) i j +
      s • complexify E i j) (complexify E i j) 0
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const (complexify E i j)).const_add
      ((1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) i j) using 1
    simp
  have hd := hasDerivAt_complexDet_identity (fun s => complexify (B s)) (complexify E) 0
    (by rw [hB0, complexify_one]) hC
  have hr := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hd).mul_const (mooreDet n A)
  have hf : (fun s => mooreDet n (B s * A * (B s)ᴴ)) =
      fun s => (complexify (B s)).det.re * mooreDet n A := by
    funext s
    exact mooreDet_congruence n A (B s)
  rw [hf] at hm
  exact hm.unique hr

theorem quaternionMatrix_conjTranspose_real_smul {I J : Type*}
    (s : ℝ) (A : Matrix I J (Quaternion ℝ)) : (s • A)ᴴ = s • Aᴴ := by
  apply Matrix.ext
  intro i j
  exact quaternionStarLinear.map_smul s (A j i)

theorem quaternionRealTrace_mul_comm (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    (∑ i, ((A * B) i i).re) = ∑ i, ((B * A) i i).re := by
  have h := congrArg Complex.re (Matrix.trace_mul_comm (complexify A) (complexify B))
  rw [← complexify_mul, ← complexify_mul, complexify_trace_real, complexify_trace_real] at h
  linarith

/-- The exact inverse-trace linearization on the Hermitian locus. `C` is an
explicit two-sided inverse of `A`, avoiding any commutative-matrix inverse
convention for quaternionic matrices. -/
theorem mooreDifferential_inverse (n : ℕ)
    (A D C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : A.IsHermitian) (hD : D.IsHermitian) (hAC : A * C = 1) (hCA : C * A = 1) :
    mooreDifferential n A D = mooreDet n A * ∑ i, ((C * D) i i).re := by
  have hAe : Aᴴ = A := hA
  have hDe : Dᴴ = D := hD
  have hCe : Cᴴ = C := by
    have hleft : Cᴴ * A = 1 := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one, hAe] using
        congrArg Matrix.conjTranspose hAC
    calc
      Cᴴ = Cᴴ * (A * C) := by rw [hAC, Matrix.mul_one]
      _ = (Cᴴ * A) * C := (Matrix.mul_assoc _ _ _).symm
      _ = C := by rw [hleft, Matrix.one_mul]
  let E : Matrix (Fin n) (Fin n) (Quaternion ℝ) := (1 / 2 : ℝ) • (D * C)
  have hEL : E * A = (1 / 2 : ℝ) • D := by
    dsimp only [E]
    rw [Matrix.smul_mul, Matrix.mul_assoc, hCA, Matrix.mul_one]
  have hER : A * Eᴴ = (1 / 2 : ℝ) • D := by
    dsimp only [E]
    rw [quaternionMatrix_conjTranspose_real_smul, Matrix.conjTranspose_mul, hCe, hDe,
      Matrix.mul_smul, ← Matrix.mul_assoc, hAC, Matrix.one_mul]
  have hE : E * A + A * Eᴴ = D := by
    rw [hEL, hER, ← add_smul]
    norm_num
  have htrace : (complexify E).trace.re = ∑ i, ((C * D) i i).re := by
    rw [complexify_trace_real]
    calc
      2 * ∑ i : Fin n, (E i i).re = 2 * ∑ i : Fin n, (1 / 2 : ℝ) * ((D * C) i i).re := rfl
      _ = ∑ i : Fin n, ((D * C) i i).re := by rw [← Finset.mul_sum]; ring
      _ = _ := quaternionRealTrace_mul_comm n D C
  have h := mooreDifferential_congruence n A E
  rw [hE, htrace] at h
  exact h.trans (mul_comm _ _)

end OAI.LinearAlgebra.Moore
