import OAI.LinearAlgebra.Moore.Basic
import OAI.Analysis.PDE.Energy.Algebra

/-! Rank-one affineness of the signed quaternionic determinant polynomial. -/

namespace OAI.LinearAlgebra.Moore

open Matrix

/-- A product is affine in a perturbation supported at at most one factor. -/
theorem prod_affine_of_sparse {I R : Type*} [Fintype I] [DecidableEq I]
    [CommRing R] (f g : I → R)
    (hg : ∀ i j, i ≠ j → g i = 0 ∨ g j = 0) (t : R) :
    (∏ i, (f i + t * g i)) =
      (∏ i, f i) + t * ((∏ i, (f i + g i)) - ∏ i, f i) := by
  classical
  by_cases hz : ∀ i, g i = 0
  · simp [hz]
  · obtain ⟨k, hk⟩ := not_forall.mp hz
    have hzero (i : I) (hi : i ≠ k) : g i = 0 := (hg i k hi).resolve_right hk
    have hp (s : R) : (∏ i, (f i + s * g i)) =
        (f k + s * g k) * ∏ i ∈ Finset.univ.erase k, f i := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      rw [hzero i (Finset.ne_of_mem_erase hi), mul_zero, add_zero]
    have hbase : (∏ i, f i) = f k * ∏ i ∈ Finset.univ.erase k, f i :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ k)).symm
    have hone := hp 1
    simp only [one_mul] at hone
    rw [hp, hone, hbase]
    ring

/-- The skew matrix corresponding to a real unit diagonal quaternionic entry. -/
def pairedPerturbation (n : ℕ) (k : Fin n) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  fun i j => if i = (k, 0) ∧ j = (k, 1) then 1
    else if i = (k, 1) ∧ j = (k, 0) then -1 else 0

theorem pairedPerturbation_support (n : ℕ) (k : Fin n)
    (i j : Fin n × Fin 2) (h : pairedPerturbation n k i j ≠ 0) :
    i = (k, 0) ∨ j = (k, 0) := by
  by_contra hh
  simp only [not_or] at hh
  simp [pairedPerturbation, hh.1, hh.2] at h

theorem pairedPerturbation_sparse (n : ℕ) (k : Fin n)
    (σ : Equiv.Perm (Fin n × Fin 2)) (i j : Fin n) (hij : i ≠ j) :
    pairedPerturbation n k (σ (i, 0)) (σ (i, 1)) = 0 ∨
      pairedPerturbation n k (σ (j, 0)) (σ (j, 1)) = 0 := by
  by_contra hh
  simp only [not_or] at hh
  have hi := pairedPerturbation_support n k _ _ hh.1
  have hj := pairedPerturbation_support n k _ _ hh.2
  rcases hi with hi | hi <;> rcases hj with hj | hj
  all_goals
    have he := σ.injective (hi.trans hj.symm)
    exact hij (congrArg Prod.fst he)

/-- Affine dependence of the Pfaffian on one distinguished skew pair. -/
theorem pfaffian_add_paired (n : ℕ)
    (M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) (k : Fin n) (t : ℂ) :
    pfaffian n (M + t • pairedPerturbation n k) =
      pfaffian n M + t * (pfaffian n (M + pairedPerturbation n k) - pfaffian n M) := by
  unfold pfaffian
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [prod_affine_of_sparse _ _ (pairedPerturbation_sparse n k _)]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_left_comm _ t]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Unit quaternionic rank-one diagonal projector. -/
def coordinateProjector (n : ℕ) (k : Fin n) : Matrix (Fin n) (Fin n) (Quaternion ℝ) :=
  fun i j => if i = k ∧ j = k then 1 else 0

theorem skewComplexify_coordinateProjector (n : ℕ) (k : Fin n) :
    skewComplexify (coordinateProjector n k) = pairedPerturbation n k := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hi : i = k <;> by_cases hj : j = k <;>
    fin_cases a <;> fin_cases b <;>
    simp [coordinateProjector, pairedPerturbation, skewComplexify, skewQuaternion,
      quaternionMatrix, symplecticUnit, Matrix.mul_apply, Fin.sum_univ_two, hi, hj] <;> rfl

theorem skewComplexify_add {I : Type*} (A B : Matrix I I (Quaternion ℝ)) :
    skewComplexify (A + B) = skewComplexify A + skewComplexify B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  change ((quaternionMatrix (A i j + B i j)) * symplecticUnit) a b = _
  rw [quaternionMatrix_add, Matrix.add_mul]
  rfl

theorem skewComplexify_real_smul {I : Type*} (A : Matrix I I (Quaternion ℝ)) (s : ℝ) :
    skewComplexify (s • A) = (s : ℂ) • skewComplexify A := by
  ext ⟨i, a⟩ ⟨j, b⟩
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M a b)
    (skewQuaternion_smul s (A i j))

/-- The signed Moore determinant is affine in each real diagonal coordinate. -/
theorem mooreDet_add_coordinate (n : ℕ) (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (k : Fin n) (t : ℝ) :
    mooreDet n (A + t • coordinateProjector n k) =
      mooreDet n A + t * (mooreDet n (A + coordinateProjector n k) - mooreDet n A) := by
  unfold mooreDet
  rw [skewComplexify_add, skewComplexify_real_smul, skewComplexify_coordinateProjector,
    pfaffian_add_paired]
  rw [skewComplexify_add, skewComplexify_coordinateProjector]
  simp

theorem pfaffian_paired_zero (n : ℕ) (k : Fin (n + 2)) :
    pfaffian (n + 2) (pairedPerturbation (n + 2) k) = 0 := by
  have hp (σ : Equiv.Perm (Fin (n + 2) × Fin 2)) :
      (∏ i : Fin (n + 2), pairedPerturbation (n + 2) k (σ (i, 0)) (σ (i, 1))) = 0 := by
    rcases pairedPerturbation_sparse (n + 2) k σ 0 1 (by simp) with h | h
    · exact Finset.prod_eq_zero (Finset.mem_univ 0) h
    · exact Finset.prod_eq_zero (Finset.mem_univ 1) h
  simp [pfaffian, hp]

theorem mooreDet_coordinateProjector_zero (n : ℕ) (k : Fin (n + 2)) :
    mooreDet (n + 2) (coordinateProjector (n + 2) k) = 0 := by
  rw [mooreDet, skewComplexify_coordinateProjector, pfaffian_paired_zero]
  rfl

/-- Exact two-parameter rank-one formula, valid in arbitrary quaternionic dimension
at least two, for the signed Moore polynomial. -/
theorem mooreDet_rankOne_pencil (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) (Quaternion ℝ))
    (k : Fin (n + 2)) (t s : ℝ) :
    mooreDet (n + 2) (t • A + s • coordinateProjector (n + 2) k) =
      t ^ (n + 2) * mooreDet (n + 2) A +
      s * t ^ (n + 1) *
        (mooreDet (n + 2) (A + coordinateProjector (n + 2) k) - mooreDet (n + 2) A) := by
  by_cases ht : t = 0
  · simp [ht, mooreDet_smul, mooreDet_coordinateProjector_zero]
  · have hm : t • A + s • coordinateProjector (n + 2) k =
        t • (A + (s / t) • coordinateProjector (n + 2) k) := by
      rw [smul_add, smul_smul]
      congr 1
      rw [mul_div_cancel₀ s ht]
    rw [hm, mooreDet_smul, mooreDet_add_coordinate]
    have hpow : t ^ (n + 2) = t ^ (n + 1) * t := pow_succ t (n + 1)
    rw [hpow]
    field_simp

/-- The determinant polynomial on the time-projector segment has only its
top two powers, with the correct signed cofactor coefficient. -/
theorem mooreDet_rankOne_segment (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) (Quaternion ℝ))
    (k : Fin (n + 2)) (t : ℝ) :
    mooreDet (n + 2) (t • A + (1 - t) • coordinateProjector (n + 2) k) =
      t ^ (n + 2) * mooreDet (n + 2) A +
      (1 - t) * t ^ (n + 1) *
        (mooreDet (n + 2) (A + coordinateProjector (n + 2) k) - mooreDet (n + 2) A) :=
  mooreDet_rankOne_pencil n A k t (1 - t)

/-- The diagonal cofactor is the genuine derivative of the Moore polynomial. -/
theorem hasDerivAt_mooreDet_coordinate (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (k : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => mooreDet n (A + s • coordinateProjector n k))
      (mooreDet n (A + coordinateProjector n k) - mooreDet n A) t := by
  have hf : (fun s : ℝ => mooreDet n (A + s • coordinateProjector n k)) =
      fun s => mooreDet n A + s *
        (mooreDet n (A + coordinateProjector n k) - mooreDet n A) := by
    funext s
    exact mooreDet_add_coordinate n A k s
  rw [hf]
  convert! ((hasDerivAt_id t).mul_const
    (mooreDet n (A + coordinateProjector n k) - mooreDet n A)).const_add
      (mooreDet n A) using 1
  simp

/-- Exact integral of the rank-one segment, the algebraic identity behind the
determinant energy in `sections/energy.tex`. -/
theorem integral_mooreDet_rankOne_segment (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) (Quaternion ℝ))
    (k : Fin (n + 2)) :
    (∫ t in (0 : ℝ)..1,
      mooreDet (n + 2) (t • A + (1 - t) • coordinateProjector (n + 2) k)) =
      mooreDet (n + 2) A / ((n : ℝ) + 3) +
      (mooreDet (n + 2) (A + coordinateProjector (n + 2) k) - mooreDet (n + 2) A) /
        (((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have hf : (fun t : ℝ =>
      mooreDet (n + 2) (t • A + (1 - t) • coordinateProjector (n + 2) k)) =
      fun t => t ^ ((n + 1) + 1) * mooreDet (n + 2) A +
        t ^ (n + 1) * (1 - t) *
          (mooreDet (n + 2) (A + coordinateProjector (n + 2) k) - mooreDet (n + 2) A) := by
    funext t
    rw [mooreDet_rankOne_segment]
    ring
  rw [hf, OAI.Analysis.PDE.Energy.integral_segment]
  norm_num [Nat.cast_add, Nat.cast_one]
  congr 2 <;> ring

end OAI.LinearAlgebra.Moore
