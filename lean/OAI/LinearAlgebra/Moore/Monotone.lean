import OAI.LinearAlgebra.Moore.Positive

/-! Strict ellipticity and determinant monotonicity on the positive cone. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix Set
open scoped MatrixOrder ComplexOrder

theorem complexify_zero {m n : Type*} :
    complexify (0 : Matrix m n (Quaternion ℝ)) = 0 := by
  apply Matrix.ext
  intro ⟨i, a⟩ ⟨j, b⟩
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M a b) quaternionMatrix_zero

theorem complex_congruence_diag {ι : Type*} [Fintype ι]
    (A C : Matrix ι ι ℂ) (i : ι) :
    (C * A * Cᴴ) i i =
      star (fun j ↦ star (C i j)) ⬝ᵥ A *ᵥ (fun j ↦ star (C i j)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, star_star, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- A positive definite matrix has strictly positive trace pairing with every
nonzero positive semidefinite matrix. -/
theorem complex_trace_mul_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosDef) (hB : B.PosSemidef) (hB0 : B ≠ 0) :
    0 < (A * B).trace.re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [star_eq_conjTranspose] at hB0 ⊢
  have hC0 : C ≠ 0 := by
    intro h
    apply hB0
    simp [h]
  obtain ⟨i, j, hij⟩ : ∃ i j, C i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hC0 (Matrix.ext h)
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hP := hA.posSemidef.mul_mul_conjTranspose_same C
  have heq : (C * A * Cᴴ).trace.re = ∑ k, ((C * A * Cᴴ) k k).re := by
    simp [Matrix.trace]
  rw [heq]
  apply Finset.sum_pos'
  · intro k _
    exact (Complex.nonneg_iff.mp (hP.diag_nonneg (i := k))).1
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [complex_congruence_diag]
    apply (Complex.pos_iff.mp (hA.dotProduct_mulVec_pos ?_)).1
    intro h
    have he := congrFun h j
    simp only [Pi.zero_apply, star_eq_zero] at he
    exact hij he

theorem mooreDifferential_nonneg_of_posDef {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hD : (complexify D).PosSemidef) :
    0 ≤ mooreDifferential n A D := by
  obtain ⟨C, hAC, hCA⟩ := exists_quaternion_inverse_of_complexify_posDef A hA
  exact mooreDifferential_nonneg n A D C hA hD hAC hCA
    (mooreDet_pos_of_complexify_posDef A hA).le

theorem mooreDifferential_pos_of_posDef {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hD : (complexify D).PosSemidef) (hD0 : D ≠ 0) :
    0 < mooreDifferential n A D := by
  rw [mooreDifferential_eq_complex_inverse A D hA (isHermitian_of_complexify hD.isHermitian)]
  apply mul_pos (mooreDet_pos_of_complexify_posDef A hA)
  apply div_pos _ (by norm_num)
  apply complex_trace_mul_pos hA.inv hD
  intro he
  apply hD0
  apply complexify_injective
  exact he.trans complexify_zero.symm

theorem hasDerivAt_mooreDet_affine {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (t : ℝ) :
    HasDerivAt (fun s ↦ mooreDet n (A + s • D)) (mooreDifferential n (A + t • D) D) t := by
  apply hasDerivAt_mooreDet_path
  intro i j
  convert! (hasDerivAt_const t (A i j)).add ((hasDerivAt_id t).smul_const (D i j)) using 1
  simp

/-- Monotonicity in every positive semidefinite direction, with no extra
determinant sign or inverse assumptions. -/
theorem mooreDet_le_of_posSemidef_difference {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hD : (complexify (B - A)).PosSemidef) :
    mooreDet n A ≤ mooreDet n B := by
  let D := B - A
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (complexify (A + t • D)).PosDef := by
    rw [complexify_add, complexify_real_smul]
    exact hA.add_posSemidef (hD.smul ht.1)
  have hcont : ContinuousOn (fun t ↦ mooreDet n (A + t • D)) (Icc (0 : ℝ) 1) :=
    fun t _ ↦ (hasDerivAt_mooreDet_affine A D t).continuousAt.continuousWithinAt
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1) hcont
    (fun t _ ↦ (hasDerivAt_mooreDet_affine A D t).hasDerivWithinAt)
    (fun t ht ↦ mooreDifferential_nonneg_of_posDef _ _ (hpos t (interior_subset ht)) hD)
  simpa [D] using hm (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) zero_le_one

/-- Strict determinant increase for every nonzero positive semidefinite direction. -/
theorem mooreDet_lt_of_posSemidef_difference {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hD : (complexify (B - A)).PosSemidef) (hBA : B ≠ A) :
    mooreDet n A < mooreDet n B := by
  let D := B - A
  have hD0 : D ≠ 0 := sub_ne_zero.mpr hBA
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (complexify (A + t • D)).PosDef := by
    rw [complexify_add, complexify_real_smul]
    exact hA.add_posSemidef (hD.smul ht.1)
  have hcont : ContinuousOn (fun t ↦ mooreDet n (A + t • D)) (Icc (0 : ℝ) 1) :=
    fun t _ ↦ (hasDerivAt_mooreDet_affine A D t).continuousAt.continuousWithinAt
  have hm := strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (0 : ℝ) 1) hcont
    (fun t _ ↦ (hasDerivAt_mooreDet_affine A D t).hasDerivWithinAt)
    (fun t ht ↦ mooreDifferential_pos_of_posDef _ _ (hpos t (interior_subset ht)) hD hD0)
  simpa [D] using hm (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) zero_lt_one

end OAI.LinearAlgebra.Moore
