import Mathlib

/-!
The faithful complex representation needed for a signed Moore determinant.
The representation is algebraic in arbitrary matrix dimension. The intended
determinant is the Pfaffian of the associated complex skew-symmetric matrix,
not a nonnegative root of its ordinary determinant.
-/

namespace OAI.LinearAlgebra.Moore

open Matrix

/-- Standard faithful complex representation of the real quaternions. -/
def quaternionMatrix (q : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]

theorem quaternionMatrix_add (p q : Quaternion ℝ) :
    quaternionMatrix (p + q) = quaternionMatrix p + quaternionMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quaternionMatrix] <;> ring

theorem quaternionMatrix_zero : quaternionMatrix 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quaternionMatrix]

theorem quaternionMatrix_one : quaternionMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quaternionMatrix]

theorem quaternionMatrix_mul (p q : Quaternion ℝ) :
    quaternionMatrix (p * q) = quaternionMatrix p * quaternionMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [quaternionMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The representation respects the full noncommutative quaternion algebra. -/
def quaternionMatrixHom : Quaternion ℝ →+* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := quaternionMatrix
  map_zero' := quaternionMatrix_zero
  map_one' := quaternionMatrix_one
  map_add' := quaternionMatrix_add
  map_mul' := quaternionMatrix_mul

theorem quaternionMatrix_star (q : Quaternion ℝ) :
    quaternionMatrix (star q) = (quaternionMatrix q)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quaternionMatrix]

theorem quaternionMatrix_injective : Function.Injective quaternionMatrix := by
  intro p q h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  have hr := congrArg Complex.re h00
  have hi := congrArg Complex.im h00
  have hj := congrArg Complex.re h01
  have hk := congrArg Complex.im h01
  exact Quaternion.ext p q hr hi hj hk

/-- Complexification of a rectangular quaternionic matrix in interleaved order. -/
def complexify {m n : Type*} (A : Matrix m n (Quaternion ℝ)) :
    Matrix (m × Fin 2) (n × Fin 2) ℂ :=
  fun i j => quaternionMatrix (A i.1 j.1) i.2 j.2

theorem complexify_add {m n : Type*} (A B : Matrix m n (Quaternion ℝ)) :
    complexify (A + B) = complexify A + complexify B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M a b)
    (quaternionMatrix_add (A i j) (B i j))

theorem complexify_star {m n : Type*} (A : Matrix m n (Quaternion ℝ)) :
    complexify Aᴴ = (complexify A)ᴴ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M a b)
    (quaternionMatrix_star (A j i))

theorem complexify_injective {m n : Type*} :
    Function.Injective (complexify : Matrix m n (Quaternion ℝ) → _) := by
  intro A B h
  funext i j
  apply quaternionMatrix_injective
  ext a b
  exact congrArg (fun M : Matrix (m × Fin 2) (n × Fin 2) ℂ => M (i, a) (j, b)) h

theorem complexify_mul {m n p : Type*} [Fintype n]
    (A : Matrix m n (Quaternion ℝ)) (B : Matrix n p (Quaternion ℝ)) :
    complexify (A * B) = complexify A * complexify B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  change quaternionMatrixHom (∑ k, A i k * B k j) a b =
    ∑ k : n × Fin 2, quaternionMatrix (A i k.1) a k.2 * quaternionMatrix (B k.1 j) k.2 b
  simp only [map_sum, map_mul, Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  rfl

/-- Quaternionic Hermitian matrices become complex Hermitian matrices. -/
theorem complexify_isHermitian {n : Type*} {A : Matrix n n (Quaternion ℝ)}
    (hA : A.IsHermitian) : (complexify A).IsHermitian := by
  rw [Matrix.IsHermitian, ← complexify_star, hA]

/-- The standard complex symplectic block, with Pfaffian normalized to one. -/
def symplecticUnit : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

def skewQuaternion (q : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  quaternionMatrix q * symplecticUnit

theorem skewQuaternion_star (q : Quaternion ℝ) :
    skewQuaternion (star q) = -(skewQuaternion q)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [skewQuaternion, quaternionMatrix, symplecticUnit, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Block form of `χ(A) J`, in interleaved order. -/
def skewComplexify {n : Type*} (A : Matrix n n (Quaternion ℝ)) :
    Matrix (n × Fin 2) (n × Fin 2) ℂ :=
  fun i j => skewQuaternion (A i.1 j.1) i.2 j.2

/-- Hermitian quaternionic matrices produce skew-symmetric complex matrices. -/
theorem skewComplexify_transpose {n : Type*} {A : Matrix n n (Quaternion ℝ)}
    (hA : A.IsHermitian) : (skewComplexify A)ᵀ = -skewComplexify A := by
  ext ⟨i, a⟩ ⟨j, b⟩
  have hij : A j i = star (A i j) := by
    simpa only [Matrix.conjTranspose_apply] using congrArg (fun M => M j i) hA.symm
  change skewQuaternion (A j i) b a = -(skewQuaternion (A i j) a b)
  rw [hij, skewQuaternion_star]
  rfl

/-- Explicit Pfaffian polynomial on paired indices. The normalization divides
out the `2^n n!` choices of orientation and ordering of the matching pairs. -/
noncomputable def pfaffian (n : ℕ)
    (M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) : ℂ :=
  (2 ^ n * (n.factorial : ℂ))⁻¹ *
    ∑ σ : Equiv.Perm (Fin n × Fin 2),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin n, M (σ (i, 0)) (σ (i, 1))

/-- Signed Moore determinant candidate, defined by the explicit Pfaffian
polynomial. Proving its full determinant identities remains separate work. -/
noncomputable def mooreDet (n : ℕ) (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) : ℝ :=
  (pfaffian n (skewComplexify A)).re

/-- The Pfaffian is homogeneous of degree `n`, including on indefinite data. -/
theorem pfaffian_smul (n : ℕ) (c : ℂ)
    (M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    pfaffian n (c • M) = c ^ n * pfaffian n M := by
  unfold pfaffian
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [mul_left_comm _ (c ^ n)]
  rw [← Finset.mul_sum]
  ring

theorem pfaffian_zero (n : ℕ) : pfaffian (n + 1) 0 = 0 := by
  simp [pfaffian]

/-- Simultaneous permutation of rows and columns changes the Pfaffian by the
permutation sign. This is the elementary congruence law for the signed polynomial. -/
theorem pfaffian_reindex (n : ℕ)
    (M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ)
    (τ : Equiv.Perm (Fin n × Fin 2)) :
    pfaffian n (M.submatrix τ τ) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) * pfaffian n M := by
  have hs : ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 := by
    have hz : (Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign τ : ℤ) = 1 := by
      simp
    exact_mod_cast hz
  unfold pfaffian
  have he :
      (∑ σ : Equiv.Perm (Fin n × Fin 2),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin n, M (τ (σ (i, 0))) (τ (σ (i, 1)))) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) *
        ∑ σ : Equiv.Perm (Fin n × Fin 2),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin n, M (σ (i, 0)) (σ (i, 1)) := by
    calc
      _ = ((Equiv.Perm.sign τ : ℤ) : ℂ) *
          ∑ σ : Equiv.Perm (Fin n × Fin 2),
            ((Equiv.Perm.sign (τ * σ) : ℤ) : ℂ) *
              ∏ i : Fin n, M ((τ * σ) (i, 0)) ((τ * σ) (i, 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro σ _
        simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, Equiv.Perm.mul_apply]
        symm
        calc
          _ = (((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
              (((Equiv.Perm.sign σ : ℤ) : ℂ) *
                ∏ i : Fin n, M (τ (σ (i, 0))) (τ (σ (i, 1)))) := by ring
          _ = _ := by rw [hs, one_mul]
      _ = _ := by
        congr 1
        exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ =>
          ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin n, M (σ (i, 0)) (σ (i, 1)))
  simp only [Matrix.submatrix_apply]
  rw [he]
  ring

/-- Scaling the row and matching column by each `c i` scales the Pfaffian
by the product of these factors. -/
theorem pfaffian_diagonal_congruence (n : ℕ)
    (M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ)
    (c : Fin n × Fin 2 → ℂ) :
    pfaffian n (of fun i j => c i * M i j * c j) =
      (∏ i, c i) * pfaffian n M := by
  have hp (σ : Equiv.Perm (Fin n × Fin 2)) :
      (∏ i : Fin n, c (σ (i, 0))) * (∏ i : Fin n, c (σ (i, 1))) = ∏ i, c i := by
    rw [← Finset.prod_mul_distrib]
    simpa only [Fintype.prod_prod_type, Fin.prod_univ_two] using Equiv.prod_comp σ c
  unfold pfaffian
  simp only [of_apply, Finset.prod_mul_distrib]
  have ht (σ : Equiv.Perm (Fin n × Fin 2)) :
      ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ((∏ i : Fin n, c (σ (i, 0))) * (∏ i : Fin n, M (σ (i, 0)) (σ (i, 1))) *
            ∏ i : Fin n, c (σ (i, 1))) =
      (∏ i, c i) * (((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∏ i : Fin n, M (σ (i, 0)) (σ (i, 1))) := by
    rw [← hp σ]
    ring
  simp_rw [ht]
  rw [← Finset.mul_sum]
  ring

/-- The one-pair Pfaffian has the expected signed normalization. -/
theorem pfaffian_one
    (M : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ) :
    pfaffian 1 M = (M (0, 0) (0, 1) - M (0, 1) (0, 0)) / 2 := by
  have hab : ((0, 0) : Fin 1 × Fin 2) ≠ (0, 1) := by decide
  have hp : (1 : Equiv.Perm (Fin 1 × Fin 2)) ≠ Equiv.swap (0, 0) (0, 1) := by
    intro h
    have hx := congrArg (fun e : Equiv.Perm (Fin 1 × Fin 2) => e (0, 0)) h
    simp at hx
  have hu : ({1, Equiv.swap ((0, 0) : Fin 1 × Fin 2) (0, 1)} :
      Finset (Equiv.Perm (Fin 1 × Fin 2))) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hp, Fintype.card_perm]
  unfold pfaffian
  rw [← hu]
  simp [hp, Equiv.Perm.sign_swap hab]
  ring

/-- For a one-by-one quaternionic matrix, the construction gives the real
part of its sole entry. In particular, negative real entries stay negative. -/
theorem mooreDet_one (A : Matrix (Fin 1) (Fin 1) (Quaternion ℝ)) :
    mooreDet 1 A = (A 0 0).re := by
  rw [mooreDet, pfaffian_one]
  simp [skewComplexify, skewQuaternion, quaternionMatrix, symplecticUnit,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem skewQuaternion_smul (c : ℝ) (q : Quaternion ℝ) :
    skewQuaternion (c • q) = (c : ℂ) • skewQuaternion q := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [skewQuaternion, quaternionMatrix, symplecticUnit, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem mooreDet_smul (n : ℕ) (c : ℝ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    mooreDet n (c • A) = c ^ n * mooreDet n A := by
  have h : skewComplexify (c • A) = (c : ℂ) • skewComplexify A := by
    ext ⟨i, a⟩ ⟨j, b⟩
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M a b)
      (skewQuaternion_smul c (A i j))
  unfold mooreDet
  rw [h, pfaffian_smul, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- A complex bilinear form viewed as a two-variable multilinear map. -/
def pairingMultilinear {I : Type*} [Fintype I] (M : Matrix I I ℂ) :
    MultilinearMap ℂ (fun _ : Fin 2 => I → ℂ) ℂ :=
  MultilinearMap.mk' (fun v => v 0 ⬝ᵥ (M *ᵥ v 1))
    (by
      intro v i x y
      fin_cases i <;>
        simp [Function.update, add_dotProduct, dotProduct_add, Matrix.mulVec_add])
    (by
      intro v i c x
      fin_cases i <;>
        simp [Function.update, smul_dotProduct, dotProduct_smul, Matrix.mulVec_smul])

/-- Product of the `n` paired bilinear evaluations, before antisymmetrization. -/
def pairProduct (n : ℕ) (M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    MultilinearMap ℂ (fun _ : Fin n × Fin 2 => (Fin n × Fin 2) → ℂ) ℂ :=
  (((MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compMultilinearMap
    (fun _ => pairingMultilinear M)).domDomCongr (Equiv.sigmaEquivProd (Fin n) (Fin 2)))

theorem pairProduct_apply (n : ℕ)
    (M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ)
    (v : (Fin n × Fin 2) → (Fin n × Fin 2) → ℂ) :
    pairProduct n M v = ∏ i : Fin n, v (i, 0) ⬝ᵥ (M *ᵥ v (i, 1)) := by
  rfl

/-- The normalized alternating form whose evaluation on the standard basis
is the Pfaffian. This supplies the route to general congruence invariance. -/
noncomputable def pfaffianAlternating (n : ℕ)
    (M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    AlternatingMap ℂ ((Fin n × Fin 2) → ℂ) ℂ (Fin n × Fin 2) :=
  (2 ^ n * (n.factorial : ℂ))⁻¹ • (pairProduct n M).alternatization

theorem pfaffianAlternating_apply (n : ℕ)
    (M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ)
    (v : (Fin n × Fin 2) → (Fin n × Fin 2) → ℂ) :
    pfaffianAlternating n M v =
      pfaffian n (of fun i j => v i ⬝ᵥ (M *ᵥ v j)) := by
  simp only [pfaffianAlternating, AlternatingMap.smul_apply,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    pairProduct_apply, pfaffian, of_apply, smul_eq_mul,
    Units.smul_def, zsmul_eq_mul]

theorem pfaffianAlternating_basis (n : ℕ)
    (M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    pfaffianAlternating n M (Pi.basisFun ℂ (Fin n × Fin 2)) = pfaffian n M := by
  rw [pfaffianAlternating_apply]
  congr 1
  ext i j
  simp [Pi.basisFun_apply, dotProduct, Matrix.mulVec, Pi.single_apply]

/-- General congruence formula for the Pfaffian. It follows from the universal
determinant characterization of alternating top-degree multilinear forms. -/
theorem pfaffian_congruence (n : ℕ)
    (M B : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    pfaffian n (B * M * Bᵀ) = B.det * pfaffian n M := by
  have hb : (of fun i j => B i ⬝ᵥ (M *ᵥ B j)) = B * M * Bᵀ := by
    ext i j
    simp only [of_apply, Matrix.mul_apply, transpose_apply, dotProduct, mulVec,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have ht := (pfaffianAlternating n M).eq_smul_basis_det
    (Pi.basisFun ℂ (Fin n × Fin 2))
  have he := congrArg (fun f : AlternatingMap ℂ ((Fin n × Fin 2) → ℂ) ℂ (Fin n × Fin 2) =>
    f (fun i j => B i j)) ht
  rw [AlternatingMap.smul_apply, pfaffianAlternating_basis, Pi.basisFun_det_apply,
    pfaffianAlternating_apply, hb] at he
  change pfaffian n (B * M * Bᵀ) = pfaffian n M * B.det at he
  exact he.trans (mul_comm _ _)

/-- The block diagonal symplectic matrix in interleaved coordinates. -/
def symplecticMatrix (n : ℕ) : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  of fun i j => if i.1 = j.1 then symplecticUnit i.2 j.2 else 0

theorem complexify_mul_symplectic (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    complexify A * symplecticMatrix n = skewComplexify A := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, complexify, symplecticMatrix,
    skewComplexify, skewQuaternion, mul_ite]

theorem symplectic_mul_transpose (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    symplecticMatrix n * (complexify A)ᵀ = complexify Aᴴ * symplecticMatrix n := by
  rw [complexify_mul_symplectic]
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, symplecticMatrix, of_apply,
    Matrix.transpose_apply, complexify, skewComplexify, Matrix.conjTranspose_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change (symplecticUnit * (quaternionMatrix (A j i))ᵀ) a b =
    skewQuaternion (star (A j i)) a b
  rw [skewQuaternion_star, skewQuaternion, Matrix.transpose_mul]
  have hj : symplecticUnitᵀ = -symplecticUnit := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symplecticUnit]
  rw [hj, Matrix.neg_mul, neg_neg]

/-- Quaternionic Hermitian congruence is carried to ordinary complex
skew-symmetric congruence by the faithful representation. -/
theorem skewComplexify_congruence (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    skewComplexify (B * A * Bᴴ) =
      complexify B * skewComplexify A * (complexify B)ᵀ := by
  rw [← complexify_mul_symplectic, complexify_mul, complexify_mul]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← symplectic_mul_transpose]
  rw [← complexify_mul_symplectic n A]
  simp only [Matrix.mul_assoc]

/-- Full quaternionic congruence law for the signed complex Pfaffian polynomial. -/
theorem quaternionic_pfaffian_congruence (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    pfaffian n (skewComplexify (B * A * Bᴴ)) =
      (complexify B).det * pfaffian n (skewComplexify A) := by
  rw [skewComplexify_congruence, pfaffian_congruence]

theorem det_symplecticMatrix (n : ℕ) : (symplecticMatrix n).det = 1 := by
  have hk : symplecticMatrix n =
      Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) symplecticUnit := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [symplecticMatrix, Matrix.one_apply, ite_mul]
  rw [hk]
  change (Matrix.kroneckerMap (fun x y : ℂ => x * y)
    (1 : Matrix (Fin n) (Fin n) ℂ) symplecticUnit).det = 1
  have hd := Matrix.det_kronecker (1 : Matrix (Fin n) (Fin n) ℂ) symplecticUnit
  have hj : symplecticUnit.det = 1 := by norm_num [symplecticUnit, Matrix.det_fin_two]
  simpa only [Matrix.det_one, hj, one_pow, mul_one] using hd

/-- The determinant of the faithful complex representation is real. -/
theorem complexify_det_real (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    (complexify A).det.im = 0 := by
  have h := congrArg Matrix.det (symplectic_mul_transpose n A)
  rw [Matrix.det_mul, Matrix.det_mul, complexify_star, Matrix.det_conjTranspose,
    Matrix.det_transpose, det_symplecticMatrix, one_mul, mul_one] at h
  have hi := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- The real signed Moore polynomial obeys the expected congruence law. -/
theorem mooreDet_congruence (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    mooreDet n (B * A * Bᴴ) = (complexify B).det.re * mooreDet n A := by
  unfold mooreDet
  rw [quaternionic_pfaffian_congruence, Complex.mul_re, complexify_det_real,
    zero_mul, sub_zero]

theorem pfaffian_map_star (n : ℕ)
    (M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    pfaffian n (M.map star) = star (pfaffian n M) := by
  change pfaffian n (M.map (starRingEnd ℂ)) = (starRingEnd ℂ) (pfaffian n M)
  simp only [pfaffian, map_mul, map_inv₀, map_pow, map_ofNat, map_natCast,
    map_sum, map_prod, map_intCast, Matrix.map_apply]

theorem symplecticMatrix_mul_transpose (n : ℕ) :
    symplecticMatrix n * (symplecticMatrix n)ᵀ = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    fin_cases a <;> fin_cases b <;>
      simp [symplecticMatrix, symplecticUnit, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two]
  · fin_cases a <;> fin_cases b <;>
      simp [symplecticMatrix, symplecticUnit, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, hij]

theorem skewComplexify_map_star (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    (skewComplexify A).map star = symplecticMatrix n * complexify A := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.map_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    symplecticMatrix, of_apply, complexify]
  simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  fin_cases a <;> fin_cases b <;> apply Complex.ext <;>
    simp [skewComplexify, skewQuaternion, quaternionMatrix, symplecticUnit,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The Pfaffian polynomial defining the Moore determinant is real-valued.
Taking its real part in `mooreDet` therefore loses no information. -/
theorem quaternionic_pfaffian_real (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    (pfaffian n (skewComplexify A)).im = 0 := by
  have hm : (skewComplexify A).map star =
      symplecticMatrix n * skewComplexify A * (symplecticMatrix n)ᵀ := by
    rw [skewComplexify_map_star, ← complexify_mul_symplectic]
    simp only [Matrix.mul_assoc, symplecticMatrix_mul_transpose, Matrix.mul_one]
  have h := pfaffian_congruence n (skewComplexify A) (symplecticMatrix n)
  rw [← hm, pfaffian_map_star, det_symplecticMatrix, one_mul] at h
  have hi := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

end OAI.LinearAlgebra.Moore
