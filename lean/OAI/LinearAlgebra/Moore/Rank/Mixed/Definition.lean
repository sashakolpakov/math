import OAI.LinearAlgebra.Moore.Cofactor

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix

/-- One real-linear entry of the skew complexification. -/
def skewMatrixEntryLinear (m : ℕ) (i j : Fin m × Fin 2) :
    Matrix (Fin m) (Fin m) (Quaternion ℝ) →ₗ[ℝ] ℂ where
  toFun A := skewComplexify A i j
  map_add' A B := by
    rw [skewComplexify_add]
    rfl
  map_smul' c A := by
    rw [skewComplexify_real_smul]
    simp

/-- The multilinear form obtained by giving each Pfaffian factor its own
matrix argument, before symmetrizing those arguments. -/
def mooreMultilinear (m : ℕ) :
    MultilinearMap ℝ (fun _ : Fin m => Matrix (Fin m) (Fin m) (Quaternion ℝ)) ℝ :=
  Complex.reCLM.toLinearMap.compMultilinearMap
    ((2 ^ m * (m.factorial : ℂ))⁻¹ •
      ∑ σ : Equiv.Perm (Fin m × Fin 2),
        (((Equiv.Perm.sign σ : ℤ) : ℂ) •
          (MultilinearMap.mkPiAlgebra ℝ (Fin m) ℂ).compLinearMap
            (fun i => skewMatrixEntryLinear m (σ (i, 0)) (σ (i, 1)))))

theorem mooreMultilinear_apply (m : ℕ)
    (A : Fin m → Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    mooreMultilinear m A =
      ((2 ^ m * (m.factorial : ℂ))⁻¹ *
        ∑ σ : Equiv.Perm (Fin m × Fin 2),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) *
            ∏ i : Fin m, skewComplexify (A i) (σ (i, 0)) (σ (i, 1))).re := by
  simp [mooreMultilinear, skewMatrixEntryLinear, MultilinearMap.mkPiAlgebra_apply]

theorem mooreMultilinear_const (m : ℕ)
    (A : Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    mooreMultilinear m (fun _ => A) = mooreDet m A := by
  rw [mooreMultilinear_apply]
  rfl

/-- The normalized symmetric multilinear polarization of the actual signed
Moore determinant. It is defined on all matrices; positivity is asserted
separately for positive-semidefinite Hermitian arguments. -/
def mixedMoore (m : ℕ) :
    MultilinearMap ℝ (fun _ : Fin m => Matrix (Fin m) (Fin m) (Quaternion ℝ)) ℝ :=
  (m.factorial : ℝ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin m), (mooreMultilinear m).domDomCongr σ

theorem mixedMoore_apply (m : ℕ)
    (A : Fin m → Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    mixedMoore m A = (m.factorial : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin m), mooreMultilinear m (fun i => A (σ i)) := by
  simp [mixedMoore]

@[simp] theorem mixedMoore_const (m : ℕ)
    (A : Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    mixedMoore m (fun _ => A) = mooreDet m A := by
  rw [mixedMoore_apply]
  simp only [mooreMultilinear_const, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have h : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp

theorem mixedMoore_comp_perm (m : ℕ)
    (A : Fin m → Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (τ : Equiv.Perm (Fin m)) :
    mixedMoore m (fun i => A (τ i)) = mixedMoore m A := by
  simp only [mixedMoore_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => by rfl)

end OAI.LinearAlgebra.Moore
