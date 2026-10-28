import OAI.Analysis.PDE.Dirichlet.RigidMotion
import OAI.LinearAlgebra.Moore.Outer

open scoped Matrix

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

def normalShearRow {n : ℕ} (ν : Fin n → Q) (k : Fin n) : Fin n → Q :=
  fun j ↦ if j = k then 0 else star (ν j)

def normalShearNilpotent {n : ℕ} (ν : Fin n → Q) (k : Fin n) : Matrix (Fin n) (Fin n) Q :=
  Matrix.vecMulVec (Pi.single k 1) (normalShearRow ν k)

theorem normalShearNilpotent_sq {n : ℕ} (ν : Fin n → Q) (k : Fin n) :
    normalShearNilpotent ν k * normalShearNilpotent ν k = 0 := by
  apply Matrix.ext
  intro i j
  by_cases hi : i = k
  · subst i
    simp [normalShearNilpotent, normalShearRow, Matrix.mul_apply, Matrix.vecMulVec,
      Pi.single_apply, mul_ite, ite_mul]
  · simp [normalShearNilpotent, Matrix.mul_apply, Matrix.vecMulVec, Pi.single_apply, hi]

/-- A basis with its distinguished column equal to the normal and its other
columns tangent. Unitarity is unnecessary for the determinant argument. -/
def adaptedNormalBasis {n : ℕ} (ν : Fin n → Q) (k : Fin n) : Matrix (Fin n) (Fin n) Q :=
  OAI.LinearAlgebra.Moore.columnExtension ν k * (1 - normalShearNilpotent ν k)

theorem adaptedNormalBasis_eq {n : ℕ} (ν : Fin n → Q) (k : Fin n) :
    adaptedNormalBasis ν k = OAI.LinearAlgebra.Moore.columnExtension ν k - Matrix.vecMulVec ν (normalShearRow ν k) := by
  unfold adaptedNormalBasis normalShearNilpotent
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_vecMulVec, OAI.LinearAlgebra.Moore.columnExtension_column]

theorem adaptedNormalBasis_apply {n : ℕ} (ν : Fin n → Q) (k i j : Fin n) :
    adaptedNormalBasis ν k i j =
      if j = k then ν i else (if i = j then 1 else 0) - ν i * star (ν j) := by
  rw [adaptedNormalBasis_eq]
  by_cases hj : j = k
  · subst j
    by_cases hi : i = k <;> simp [OAI.LinearAlgebra.Moore.columnExtension, normalShearRow, Matrix.vecMulVec,
      Pi.single_apply, hi]
  · simp [OAI.LinearAlgebra.Moore.columnExtension, normalShearRow, Matrix.vecMulVec, Pi.single_apply,
      Matrix.one_apply, hj]

theorem adaptedNormalBasis_column {n : ℕ} (ν : Fin n → Q) (k : Fin n) :
    (fun i ↦ adaptedNormalBasis ν k i k) = ν := by
  funext i
  simp [adaptedNormalBasis_apply]

theorem adaptedNormalBasis_tangent {n : ℕ} (ν : Fin n → Q) (k j : Fin n)
    (hν : quaternionPairing ν ν = 1) (hj : j ≠ k) :
    quaternionPairing ν (fun i ↦ adaptedNormalBasis ν k i j) = 0 := by
  simp only [quaternionPairing, adaptedNormalBasis_apply, ite_eq_right hj, mul_sub,
    mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, ← mul_assoc, ← Finset.sum_mul]
  change star (ν j) - quaternionPairing ν ν * star (ν j) = 0
  rw [hν, one_mul, sub_self]

theorem adaptedNormalBasis_mulVec_injective {n : ℕ} (ν : Fin n → Q) (k : Fin n)
    (hk : ν k ≠ 0) : Function.Injective (Matrix.mulVec (adaptedNormalBasis ν k)) := by
  intro x y hxy
  have hS : (1 + normalShearNilpotent ν k) * (1 - normalShearNilpotent ν k) = 1 := by
    calc
      _ = 1 - normalShearNilpotent ν k * normalShearNilpotent ν k := by noncomm_ring
      _ = 1 := by rw [normalShearNilpotent_sq, sub_zero]
  have heq : (1 - normalShearNilpotent ν k) *ᵥ x =
      (1 - normalShearNilpotent ν k) *ᵥ y := by
    apply OAI.LinearAlgebra.Moore.columnExtension_mulVec_injective ν k hk
    simpa only [adaptedNormalBasis, Matrix.mulVec_mulVec] using hxy
  have h := congrArg (Matrix.mulVec (1 + normalShearNilpotent ν k)) heq
  simpa only [Matrix.mulVec_mulVec, hS, Matrix.one_mulVec] using h

/-- The adapted normal/tangent matrix is invertible whenever its selected
normal coordinate is nonzero; the inverse is built by a nilpotent shear. -/
theorem adaptedNormalBasis_right_inverse {n : ℕ} (ν : Fin n → Q) (k : Fin n)
    (hk : ν k ≠ 0) : ∃ C : Matrix (Fin n) (Fin n) Q, adaptedNormalBasis ν k * C = 1 := by
  obtain ⟨C, hC⟩ := OAI.LinearAlgebra.Moore.exists_right_inverse_of_mulVec_injective (OAI.LinearAlgebra.Moore.columnExtension ν k)
    (OAI.LinearAlgebra.Moore.columnExtension_mulVec_injective ν k hk)
  let N := normalShearNilpotent ν k
  have hN : N * N = 0 := normalShearNilpotent_sq ν k
  have hS : (1 - N) * (1 + N) = 1 := by
    calc
      _ = 1 - N * N := by noncomm_ring
      _ = 1 := by rw [hN, sub_zero]
  refine ⟨(1 + N) * C, ?_⟩
  change (OAI.LinearAlgebra.Moore.columnExtension ν k * (1 - N)) * ((1 + N) * C) = 1
  calc
    _ = OAI.LinearAlgebra.Moore.columnExtension ν k * ((1 - N) * (1 + N)) * C := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hS, Matrix.mul_one, hC]

theorem quaternionForm_congruence {n : ℕ} (A B : Matrix (Fin n) (Fin n) Q)
    (z : Fin n → Q) : quaternionForm (Bᴴ * A * B) z = quaternionForm A (B *ᵥ z) := by
  simp only [OAI.LinearAlgebra.Moore.quaternionForm_eq_dotProduct, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem quaternionPairing_mulVec {n : ℕ} (ν : Fin n → Q)
    (B : Matrix (Fin n) (Fin n) Q) (z : Fin n → Q) :
    quaternionPairing ν (B *ᵥ z) = ∑ j, quaternionPairing ν (fun i ↦ B i j) * z j := by
  simp only [quaternionPairing, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- A unit normal can be made the first column of a genuine basis whose
remaining columns are quaternionically tangent, without a spectral theorem. -/
theorem exists_normal_tangent_basis {n : ℕ} (ν : Fin (n + 1) → Q)
    (hν : quaternionPairing ν ν = 1) :
    ∃ B : Matrix (Fin (n + 1)) (Fin (n + 1)) Q,
      (fun i ↦ B i 0) = ν ∧ Function.Injective B.mulVec ∧
      (∀ j : Fin n, quaternionPairing ν (fun i ↦ B i j.succ) = 0) := by
  have hk : ∃ k, ν k ≠ 0 := by
    by_contra he
    push Not at he
    have hz : ν = 0 := funext he
    simp [hz, quaternionPairing] at hν
  obtain ⟨k, hk⟩ := hk
  obtain ⟨C, hC⟩ := adaptedNormalBasis_right_inverse ν k hk
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 k
  let B := (adaptedNormalBasis ν k).submatrix id σ
  let D := C.submatrix σ id
  have hBD : B * D = 1 := by
    dsimp only [B, D]
    rw [Matrix.submatrix_mul_equiv, hC]
    rfl
  refine ⟨B, ?_, ?_, ?_⟩
  · simpa only [B, Matrix.submatrix_apply, id_eq, σ, Equiv.swap_apply_left] using
      adaptedNormalBasis_column ν k
  · apply (LinearMap.injective_iff_surjective (f := OAI.LinearAlgebra.Moore.quaternionMulVecLinear B)).mpr
    intro y
    refine ⟨D *ᵥ y, ?_⟩
    change B *ᵥ (D *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, hBD, Matrix.one_mulVec]
  · intro j
    apply adaptedNormalBasis_tangent ν k (σ j.succ) hν
    have hs : σ 0 = k := Equiv.swap_apply_left _ _
    intro he
    have : j.succ = 0 := σ.injective (he.trans hs.symm)
    exact Fin.succ_ne_zero j this

end OAI.Analysis.PDE.Dirichlet
