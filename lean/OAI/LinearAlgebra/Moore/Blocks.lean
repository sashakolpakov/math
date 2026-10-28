import OAI.LinearAlgebra.Moore.Square
import OAI.LinearAlgebra.Moore.Outer

/-! Normal/spatial block algebra for the signed quaternionic determinant. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.PDE.Dirichlet
open scoped MatrixOrder ComplexOrder

def normalSplit (n : ℕ) : Fin (n + 1) ≃ Unit ⊕ Fin n where
  toFun := Fin.cases (Sum.inl ()) Sum.inr
  invFun := Sum.elim (fun _ ↦ 0) Fin.succ
  left_inv := by intro i; refine Fin.cases rfl (fun _ ↦ rfl) i
  right_inv := by rintro (a | i); cases a; rfl; rfl

def complexNormalSplit (n : ℕ) :
    Fin (n + 1) × Fin 2 ≃ (Unit × Fin 2) ⊕ (Fin n × Fin 2) :=
  (Equiv.prodCongr (normalSplit n) (Equiv.refl (Fin 2))).trans
    (Equiv.sumProdDistrib Unit (Fin n) (Fin 2))

def normalBlock {n : ℕ} (A : Matrix Unit Unit (Quaternion ℝ))
    (B : Matrix Unit (Fin n) (Quaternion ℝ))
    (C : Matrix (Fin n) Unit (Quaternion ℝ))
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ) :=
  (Matrix.fromBlocks A B C D).submatrix (normalSplit n) (normalSplit n)

@[simp] theorem normalBlock_zero_zero {n : ℕ} (A : Matrix Unit Unit (Quaternion ℝ))
    (B : Matrix Unit (Fin n) (Quaternion ℝ)) (C : Matrix (Fin n) Unit (Quaternion ℝ))
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) : normalBlock A B C D 0 0 = A () () := rfl

@[simp] theorem normalBlock_zero_succ {n : ℕ} (A : Matrix Unit Unit (Quaternion ℝ))
    (B : Matrix Unit (Fin n) (Quaternion ℝ)) (C : Matrix (Fin n) Unit (Quaternion ℝ))
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (j : Fin n) :
    normalBlock A B C D 0 j.succ = B () j := rfl

@[simp] theorem normalBlock_succ_zero {n : ℕ} (A : Matrix Unit Unit (Quaternion ℝ))
    (B : Matrix Unit (Fin n) (Quaternion ℝ)) (C : Matrix (Fin n) Unit (Quaternion ℝ))
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (i : Fin n) :
    normalBlock A B C D i.succ 0 = C i () := rfl

@[simp] theorem normalBlock_succ_succ {n : ℕ} (A : Matrix Unit Unit (Quaternion ℝ))
    (B : Matrix Unit (Fin n) (Quaternion ℝ)) (C : Matrix (Fin n) Unit (Quaternion ℝ))
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (i j : Fin n) :
    normalBlock A B C D i.succ j.succ = D i j := rfl

theorem complexify_one_generic {I : Type*} [DecidableEq I] :
    complexify (1 : Matrix I I (Quaternion ℝ)) = 1 := by
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases hij : i = j
  · subst j
    simp [complexify, Matrix.one_apply, quaternionMatrix_one]
  · simp [complexify, hij, quaternionMatrix_zero]

theorem normalBlock_mul {n : ℕ}
    (A E : Matrix Unit Unit (Quaternion ℝ))
    (B F : Matrix Unit (Fin n) (Quaternion ℝ))
    (C G : Matrix (Fin n) Unit (Quaternion ℝ))
    (D H : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    normalBlock A B C D * normalBlock E F G H =
      normalBlock (A * E + B * G) (A * F + B * H)
        (C * E + D * G) (C * F + D * H) := by
  unfold normalBlock
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem normalBlock_star {n : ℕ}
    (A : Matrix Unit Unit (Quaternion ℝ))
    (B : Matrix Unit (Fin n) (Quaternion ℝ))
    (C : Matrix (Fin n) Unit (Quaternion ℝ))
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    (normalBlock A B C D)ᴴ = normalBlock Aᴴ Cᴴ Bᴴ Dᴴ := by
  simp only [normalBlock, Matrix.conjTranspose_submatrix,
    Matrix.fromBlocks_conjTranspose]

theorem normalBlock_one (n : ℕ) :
    normalBlock (1 : Matrix Unit Unit (Quaternion ℝ)) 0 0
      (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) = 1 := by
  simp [normalBlock, Matrix.fromBlocks_one]

theorem complexify_normalBlock {n : ℕ}
    (A : Matrix Unit Unit (Quaternion ℝ))
    (B : Matrix Unit (Fin n) (Quaternion ℝ))
    (C : Matrix (Fin n) Unit (Quaternion ℝ))
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    complexify (normalBlock A B C D) =
      (Matrix.fromBlocks (complexify A) (complexify B) (complexify C) (complexify D)).submatrix
        (complexNormalSplit n) (complexNormalSplit n) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> rfl

theorem complexify_normalBlock_det {n : ℕ}
    (A : Matrix Unit Unit (Quaternion ℝ))
    (B : Matrix Unit (Fin n) (Quaternion ℝ))
    (C : Matrix (Fin n) Unit (Quaternion ℝ))
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    (complexify (normalBlock A B C D)).det =
      (Matrix.fromBlocks (complexify A) (complexify B) (complexify C) (complexify D)).det := by
  rw [complexify_normalBlock, Matrix.det_submatrix_equiv_self]

theorem complexify_normalBlock_upper_det {n : ℕ}
    (B : Matrix Unit (Fin n) (Quaternion ℝ)) :
    (complexify (normalBlock (1 : Matrix Unit Unit (Quaternion ℝ)) B 0
      (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).det = 1 := by
  rw [complexify_normalBlock_det, complexify_one_generic, complexify_one_generic,
    complexify_zero, Matrix.det_fromBlocks_zero₂₁]
  simp

def normalDiagonal {n : ℕ} (s : ℝ)
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :=
  normalBlock (s • (1 : Matrix Unit Unit (Quaternion ℝ))) 0 0 D

theorem normalDiagonal_isHermitian {n : ℕ} (s : ℝ)
    {D : Matrix (Fin n) (Fin n) (Quaternion ℝ)} (hD : D.IsHermitian) :
    (normalDiagonal s D).IsHermitian := by
  rw [Matrix.IsHermitian, normalDiagonal, normalBlock_star]
  simp only [quaternionMatrix_conjTranspose_real_smul, Matrix.conjTranspose_one,
    Matrix.conjTranspose_zero]
  rw [hD]

theorem normalDiagonal_quaternionForm {n : ℕ} (s : ℝ)
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (z : Fin (n + 1) → Quaternion ℝ) :
    (OAI.Analysis.PDE.Dirichlet.quaternionForm (normalDiagonal s D) z).re =
      s * Quaternion.normSq (z 0) + (OAI.Analysis.PDE.Dirichlet.quaternionForm D (fun i ↦ z i.succ)).re := by
  have h : OAI.Analysis.PDE.Dirichlet.quaternionForm (normalDiagonal s D) z =
      star (z 0) * (s • (1 : Quaternion ℝ)) * z 0 +
        OAI.Analysis.PDE.Dirichlet.quaternionForm D (fun i ↦ z i.succ) := by
    simp [OAI.Analysis.PDE.Dirichlet.quaternionForm, Fin.sum_univ_succ, normalDiagonal]
  rw [h]
  change (star (z 0) * (s • (1 : Quaternion ℝ)) * z 0).re + _ = _
  congr 1
  simp [Quaternion.star_mul_self]

theorem complexify_normalDiagonal_posDef {n : ℕ} {s : ℝ}
    (hs : 0 < s) (D : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hD : (complexify D).PosDef) : (complexify (normalDiagonal s D)).PosDef := by
  have hDH := isHermitian_of_complexify hD.isHermitian
  apply (complexify_posDef_iff (normalDiagonal_isHermitian s hDH)).mpr
  intro z hz
  rw [normalDiagonal_quaternionForm]
  have hn : 0 ≤ s * Quaternion.normSq (z 0) := mul_nonneg hs.le Quaternion.normSq_nonneg
  have ht := (complexify_posSemidef_iff hDH).mp hD.posSemidef (fun i ↦ z i.succ)
  by_cases htail : (fun i : Fin n ↦ z i.succ) = 0
  · have hz0 : z 0 ≠ 0 := by
      intro he
      apply hz
      funext i
      refine Fin.cases he (fun j ↦ ?_) i
      exact congrFun htail j
    have hp : 0 < Quaternion.normSq (z 0) :=
      lt_of_le_of_ne Quaternion.normSq_nonneg (Ne.symm (Quaternion.normSq_ne_zero.mpr hz0))
    exact add_pos_of_pos_of_nonneg (mul_pos hs hp) ht
  · exact add_pos_of_nonneg_of_pos hn ((complexify_posDef_iff hDH).mp hD _ htail)

theorem complexify_normalDiagonal_one_det {n : ℕ}
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    (complexify (normalDiagonal 1 D)).det = (complexify D).det := by
  unfold normalDiagonal
  rw [one_smul, complexify_normalBlock_det, complexify_one_generic,
    complexify_zero, complexify_zero, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem mooreDet_normalDiagonal_one {n : ℕ}
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hD : (complexify D).PosDef) :
    mooreDet (n + 1) (normalDiagonal 1 D) = mooreDet n D := by
  have hp := complexify_normalDiagonal_posDef (by norm_num : (0 : ℝ) < 1) D hD
  have hsq := mooreDet_sq_eq_complexify_det_of_posDef (normalDiagonal 1 D) hp
  rw [complexify_normalDiagonal_one_det] at hsq
  have hsqD := mooreDet_sq_eq_complexify_det_of_posDef D hD
  have ha := mooreDet_pos_of_complexify_posDef (normalDiagonal 1 D) hp
  have hb := mooreDet_pos_of_complexify_posDef D hD
  nlinarith

theorem normalDiagonal_add_coordinate {n : ℕ} (s : ℝ)
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    normalDiagonal s D = normalDiagonal 0 D + s • coordinateProjector (n + 1) 0 := by
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    refine Fin.cases ?_ (fun j ↦ ?_) j <;>
    simp [normalDiagonal, coordinateProjector]

theorem mooreDet_normalDiagonal_zero {n : ℕ}
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hD : D.IsHermitian) :
    mooreDet (n + 1) (normalDiagonal 0 D) = 0 := by
  apply mooreDet_zero_of_normalized_kernel (n + 1) (normalDiagonal 0 D)
    (normalDiagonal_isHermitian 0 hD) (Pi.single 0 1) 0 (by simp)
  funext i
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, normalDiagonal]

/-- Signed block factorization: the normal scalar is not assumed positive. -/
theorem mooreDet_normalDiagonal {n : ℕ} (s : ℝ)
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hD : (complexify D).PosDef) :
    mooreDet (n + 1) (normalDiagonal s D) = s * mooreDet n D := by
  have h0 := mooreDet_normalDiagonal_zero D (isHermitian_of_complexify hD.isHermitian)
  have h1 : normalDiagonal 0 D + coordinateProjector (n + 1) 0 = normalDiagonal 1 D := by
    simpa using (normalDiagonal_add_coordinate 1 D).symm
  rw [normalDiagonal_add_coordinate, mooreDet_add_coordinate, h0, h1,
    mooreDet_normalDiagonal_one D hD]
  ring

end OAI.LinearAlgebra.Moore
