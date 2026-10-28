import OAI.LinearAlgebra.Moore.Blocks

/-! Signed Schur complementation with an arbitrary positive quaternionic spatial block. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.PDE.Dirichlet
open scoped MatrixOrder ComplexOrder

def quaternionColumn {n : ℕ} (c : Fin n → Quaternion ℝ) :
    Matrix (Fin n) Unit (Quaternion ℝ) := fun i _ ↦ c i

def hermitianBlock {n : ℕ} (ell : ℝ) (c : Fin n → Quaternion ℝ)
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :=
  normalBlock (ell • (1 : Matrix Unit Unit (Quaternion ℝ)))
    (quaternionColumn c)ᴴ (quaternionColumn c) D

def normalShear {n : ℕ} (B : Matrix Unit (Fin n) (Quaternion ℝ)) :=
  normalBlock (1 : Matrix Unit Unit (Quaternion ℝ)) B 0
    (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ))

theorem hermitianBlock_reconstruct {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ)) (hA : A.IsHermitian) :
    A = hermitianBlock (A 0 0).re (fun i ↦ A i.succ 0) (A.submatrix Fin.succ Fin.succ) := by
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun j ↦ ?_) j
  · change A 0 0 = (A 0 0).re • (1 : Quaternion ℝ)
    rw [← Quaternion.coe_mul_eq_smul, mul_one]
    exact Quaternion.star_eq_self.mp (congrFun (congrFun hA 0) 0)
  · change A 0 j.succ = star (A j.succ 0)
    exact (congrFun (congrFun hA 0) j.succ).symm
  · rfl
  · rfl

theorem normalShear_congruence {n : ℕ} (s : ℝ)
    (B : Matrix Unit (Fin n) (Quaternion ℝ))
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    normalShear B * normalDiagonal s D * (normalShear B)ᴴ =
      normalBlock (s • 1 + B * D * Bᴴ) (B * D) (D * Bᴴ) D := by
  simp only [normalShear, normalDiagonal, normalBlock_star, normalBlock_mul,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]

theorem quaternionColumn_pairing {n : ℕ}
    (C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (c : Fin n → Quaternion ℝ) :
    ((quaternionColumn c)ᴴ * C * quaternionColumn c) () () = OAI.Analysis.PDE.Dirichlet.quaternionForm C c := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, quaternionColumn,
    OAI.Analysis.PDE.Dirichlet.quaternionForm, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem singleton_hermitian_eq_real (A : Matrix Unit Unit (Quaternion ℝ))
    (hA : A.IsHermitian) : A = (A () ()).re • 1 := by
  have hs : star (A () ()) = A () () := congrFun (congrFun hA ()) ()
  apply Matrix.ext
  rintro ⟨⟩ ⟨⟩
  change A () () = (A () ()).re • (1 : Quaternion ℝ)
  rw [← Quaternion.coe_mul_eq_smul, mul_one]
  exact Quaternion.star_eq_self.mp hs

theorem quaternionColumn_pairing_real {n : ℕ}
    (C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hC : C.IsHermitian)
    (c : Fin n → Quaternion ℝ) :
    (quaternionColumn c)ᴴ * C * quaternionColumn c = (OAI.Analysis.PDE.Dirichlet.quaternionForm C c).re • 1 := by
  rw [← quaternionColumn_pairing]
  apply singleton_hermitian_eq_real
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hC, Matrix.mul_assoc]

/-- Exact completion of the square. The full matrix may be indefinite. -/
theorem hermitianBlock_schur_congruence {n : ℕ}
    (ell : ℝ) (c : Fin n → Quaternion ℝ)
    (D C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hC : C.IsHermitian) (hDC : D * C = 1) (hCD : C * D = 1) :
    normalShear ((quaternionColumn c)ᴴ * C) *
      normalDiagonal (ell - (OAI.Analysis.PDE.Dirichlet.quaternionForm C c).re) D *
        (normalShear ((quaternionColumn c)ᴴ * C))ᴴ = hermitianBlock ell c D := by
  rw [normalShear_congruence]
  have hr : ((quaternionColumn c)ᴴ * C) * D = (quaternionColumn c)ᴴ := by
    rw [Matrix.mul_assoc, hCD, Matrix.mul_one]
  have hl : D * ((quaternionColumn c)ᴴ * C)ᴴ = quaternionColumn c := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hC,
      ← Matrix.mul_assoc, hDC, Matrix.one_mul]
  rw [hr, hl, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hC,
    ← Matrix.mul_assoc, quaternionColumn_pairing_real C hC c]
  rw [← add_smul, sub_add_cancel]
  rfl

/-- The normal Schur complement factors the signed Moore determinant. -/
theorem mooreDet_hermitianBlock {n : ℕ}
    (ell : ℝ) (c : Fin n → Quaternion ℝ)
    (D C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hD : (complexify D).PosDef) (hDC : D * C = 1) (hCD : C * D = 1) :
    mooreDet (n + 1) (hermitianBlock ell c D) =
      (ell - (OAI.Analysis.PDE.Dirichlet.quaternionForm C c).re) * mooreDet n D := by
  have hC := isHermitian_of_complexify (complexify_inverse_posDef n D C hD hDC).isHermitian
  have h := mooreDet_congruence (n + 1)
    (normalDiagonal (ell - (OAI.Analysis.PDE.Dirichlet.quaternionForm C c).re) D)
    (normalShear ((quaternionColumn c)ᴴ * C))
  rw [hermitianBlock_schur_congruence ell c D C hC hDC hCD] at h
  rw [normalShear, complexify_normalBlock_upper_det, Complex.one_re, one_mul,
    mooreDet_normalDiagonal _ D hD] at h
  exact h

/-- The equation explicitly solves for the normal-normal entry. -/
theorem hermitianBlock_normal_entry {n : ℕ}
    (ell : ℝ) (c : Fin n → Quaternion ℝ)
    (D C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hD : (complexify D).PosDef) (hDC : D * C = 1) (hCD : C * D = 1) :
    ell = mooreDet (n + 1) (hermitianBlock ell c D) / mooreDet n D +
      (OAI.Analysis.PDE.Dirichlet.quaternionForm C c).re := by
  rw [mooreDet_hermitianBlock ell c D C hD hDC hCD]
  have hm : mooreDet n D ≠ 0 := (mooreDet_pos_of_complexify_posDef D hD).ne'
  field_simp
  ring

theorem hermitianBlock_add_coordinate {n : ℕ} (ell t : ℝ)
    (c : Fin n → Quaternion ℝ) (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    hermitianBlock ell c D + t • coordinateProjector (n + 1) 0 =
      hermitianBlock (ell + t) c D := by
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    refine Fin.cases ?_ (fun j ↦ ?_) j <;>
    simp [hermitianBlock, coordinateProjector, add_smul]

/-- The normal cofactor is the determinant of the positive spatial block,
even when the full matrix is indefinite. -/
theorem mooreCofactor_hermitianBlock_normal {n : ℕ}
    (ell : ℝ) (c : Fin n → Quaternion ℝ)
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hD : (complexify D).PosDef) :
    (mooreCofactor (n + 1) (hermitianBlock ell c D) 0 0).re = mooreDet n D := by
  obtain ⟨C,hDC,hCD⟩ := exists_quaternion_inverse_of_complexify_posDef D hD
  rw [mooreCofactor_diag]
  have he := hermitianBlock_add_coordinate ell 1 c D
  simp only [one_smul] at he
  rw [he, mooreDet_hermitianBlock _ _ D C hD hDC hCD,
    mooreDet_hermitianBlock _ _ D C hD hDC hCD]
  ring

theorem complexify_normalDiagonal_zero_posSemidef {n : ℕ}
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hD : (complexify D).PosSemidef) :
    (complexify (normalDiagonal 0 D)).PosSemidef := by
  have hDH := isHermitian_of_complexify hD.isHermitian
  apply (complexify_posSemidef_iff (normalDiagonal_isHermitian 0 hDH)).mpr
  intro z
  rw [normalDiagonal_quaternionForm, zero_mul, zero_add]
  exact (complexify_posSemidef_iff hDH).mp hD _

/-- Subtracting the normal Schur complement leaves a positive semidefinite matrix. -/
theorem complexify_schur_remainder_posSemidef {n : ℕ}
    (ell : ℝ) (c : Fin n → Quaternion ℝ)
    (D C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hD : (complexify D).PosDef) (hDC : D * C = 1) (hCD : C * D = 1) :
    (complexify (hermitianBlock ell c D -
      (ell - (OAI.Analysis.PDE.Dirichlet.quaternionForm C c).re) • coordinateProjector (n + 1) 0)).PosSemidef := by
  have hC := isHermitian_of_complexify (complexify_inverse_posDef n D C hD hDC).isHermitian
  have he : hermitianBlock ell c D -
      (ell - (OAI.Analysis.PDE.Dirichlet.quaternionForm C c).re) • coordinateProjector (n + 1) 0 =
        hermitianBlock (OAI.Analysis.PDE.Dirichlet.quaternionForm C c).re c D := by
    rw [sub_eq_add_neg, ← neg_smul, hermitianBlock_add_coordinate]
    congr 1
    ring
  rw [he, ← hermitianBlock_schur_congruence _ c D C hC hDC hCD, sub_self,
    complexify_mul, complexify_mul, complexify_star]
  exact (complexify_normalDiagonal_zero_posSemidef D hD.posSemidef).mul_mul_conjTranspose_same _

theorem realTrace_mul_nonneg {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosSemidef) (hB : (complexify B).PosSemidef) :
    0 ≤ realTrace (A * B) := by
  have h := complex_trace_mul_nonneg hA hB
  rw [← complexify_mul, complexify_trace_real] at h
  change 0 ≤ (∑ i, (A * B) i i).re
  simpa only [quaternion_re_sum] using (show 0 ≤ ∑ i, ((A * B) i i).re by linarith)

theorem realTrace_mul_coordinate {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (k : Fin n) :
    realTrace (A * coordinateProjector n k) = (A k k).re := by
  rw [coordinateProjector_eq_single, realTrace_mul_single, mul_one]

/-- The central pointwise Schur inequality used in the determinant energy. -/
theorem schur_trace_inequality {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ))
    (hA : (complexify A).PosSemidef) (ell : ℝ) (c : Fin n → Quaternion ℝ)
    (D C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hD : (complexify D).PosDef) (hDC : D * C = 1) (hCD : C * D = 1) :
    (ell - (OAI.Analysis.PDE.Dirichlet.quaternionForm C c).re) * (A 0 0).re ≤
      realTrace (A * hermitianBlock ell c D) := by
  have hp := realTrace_mul_nonneg A _ hA
    (complexify_schur_remainder_posSemidef ell c D C hD hDC hCD)
  rw [Matrix.mul_sub, realTrace_sub, Matrix.mul_smul, realTrace_smul,
    realTrace_mul_coordinate] at hp
  linarith

theorem schur_determinant_energy_inequality {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ))
    (hA : (complexify A).PosSemidef) (ell : ℝ) (c : Fin n → Quaternion ℝ)
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hD : (complexify D).PosDef)
    (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hdet : mooreDet n D = lambda * (A 0 0).re) :
    mooreDet (n + 1) (hermitianBlock ell c D) ≤
      lambda * realTrace (A * hermitianBlock ell c D) := by
  obtain ⟨C,hDC,hCD⟩ := exists_quaternion_inverse_of_complexify_posDef D hD
  have hp := mul_le_mul_of_nonneg_left
    (schur_trace_inequality A hA ell c D C hD hDC hCD) hlambda
  rw [mooreDet_hermitianBlock ell c D C hD hDC hCD, hdet]
  nlinarith

end OAI.LinearAlgebra.Moore
