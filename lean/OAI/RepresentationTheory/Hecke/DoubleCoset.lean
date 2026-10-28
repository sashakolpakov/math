import OAI.RepresentationTheory.Hecke.CosetCalculusArithmeticMeasure

/-! # Double Coset -/

namespace OAI.RepresentationTheory.Hecke.DoubleCoset.Calculus

noncomputable section

section

/-! Matrix characterization of the first minuscule double coset over a DVR. -/

open scoped BigOperators

variable {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

def InDoubleCoset (π : R) (a : Fin 3 → ℤ) (M : CosetCalculusArithmeticMeasure.Mat F) : Prop :=
  ∃ U V : Matrix.GeneralLinearGroup (Fin 3) R,
    M = U.val.map (algebraMap R F) *
      Matrix.diagonal (fun i => (algebraMap R F π) ^ a i) *
      V.val.map (algebraMap R F)

def FirstCondition (π : R) (M : CosetCalculusArithmeticMeasure.Mat F) : Prop :=
  CosetCalculusArithmeticMeasure.IntegralMatrix (R := R) M ∧
    ∃ u : Rˣ, M.det = algebraMap R F (u : R) * algebraMap R F π

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
lemma integral_of_factorization_iff
    (U V : Matrix.GeneralLinearGroup (Fin 3) R) (D M : CosetCalculusArithmeticMeasure.Mat F)
    (h : M = U.val.map (algebraMap R F) * D * V.val.map (algebraMap R F)) :
    CosetCalculusArithmeticMeasure.IntegralMatrix (R := R) M ↔ CosetCalculusArithmeticMeasure.IntegralMatrix (R := R) D := by
  let f : CosetCalculusArithmeticMeasure.Mat R →+* CosetCalculusArithmeticMeasure.Mat F := (algebraMap R F).mapMatrix
  have hU : f (↑U⁻¹) * f U.val = 1 := by rw [← map_mul]; simp
  have hV : f V.val * f (↑V⁻¹) = 1 := by rw [← map_mul]; simp
  have h' : M = f U.val * D * f V.val := h
  constructor
  · intro hM
    have he : f (↑U⁻¹) * M * f (↑V⁻¹) = D := by
      rw [h']
      calc
        _ = (f (↑U⁻¹) * f U.val) * D * (f V.val * f (↑V⁻¹)) := by
          simp only [mul_assoc]
        _ = D := by rw [hU, hV, one_mul, mul_one]
    rw [← he]
    exact f.range.mul_mem (f.range.mul_mem ⟨↑U⁻¹, rfl⟩ hM) ⟨↑V⁻¹, rfl⟩
  · intro hD
    rw [h']
    exact f.range.mul_mem (f.range.mul_mem ⟨U.val, rfl⟩ hD) ⟨V.val, rfl⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma integral_diagonal_iff (π : R) (hπ : Irreducible π) (a : Fin 3 → ℤ) :
    CosetCalculusArithmeticMeasure.IntegralMatrix (R := R) (Matrix.diagonal (fun i => (algebraMap R F π) ^ a i)) ↔
      ∀ i, 0 ≤ a i := by
  rw [CosetCalculusArithmeticMeasure.integralMatrix_iff]
  constructor
  · intro h i
    exact (CosetCalculusArithmeticMeasure.integral_zpow π hπ (a i)).mp (by simpa using h i i)
  · intro h i j
    by_cases hij : i = j
    · subst j
      simpa using (CosetCalculusArithmeticMeasure.integral_zpow π hπ (a i)).mpr (h i)
    · simpa [Matrix.diagonal_apply_ne _ hij] using
        (show CosetCalculusArithmeticMeasure.IntegralElement (R := R) (0 : F) from ⟨0, map_zero _⟩)

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma factorization_det (π : R) (hπ : Irreducible π) (a : Fin 3 → ℤ)
    (U V : Matrix.GeneralLinearGroup (Fin 3) R) (M : CosetCalculusArithmeticMeasure.Mat F)
    (h : M = U.val.map (algebraMap R F) *
      Matrix.diagonal (fun i => (algebraMap R F π) ^ a i) *
      V.val.map (algebraMap R F)) :
    M.det = algebraMap R F (↑(U.det * V.det) : R) *
      (algebraMap R F π) ^ (a 0 + a 1 + a 2) := by
  have hp := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero (K := F) hπ
  have hmap (B : CosetCalculusArithmeticMeasure.Mat R) : (B.map (algebraMap R F)).det = algebraMap R F B.det :=
    ((algebraMap R F).map_det B).symm
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  rw [hmap, hmap]
  simp only [Fin.prod_univ_succ, Fin.isValue,
    Units.val_mul, map_mul, zpow_add₀ hp]
  change algebraMap R F U.val.det *
    ((algebraMap R F π) ^ a 0 * ((algebraMap R F π) ^ a 1 *
      ((algebraMap R F π) ^ a 2 * 1))) * algebraMap R F V.val.det =
    (algebraMap R F U.val.det * algebraMap R F V.val.det) *
      ((algebraMap R F π) ^ a 0 * (algebraMap R F π) ^ a 1 * (algebraMap R F π) ^ a 2)
  ring

theorem firstCondition_iff_doubleCoset (π : R) (hπ : Irreducible π) (M : CosetCalculusArithmeticMeasure.Mat F) :
    FirstCondition π M ↔ InDoubleCoset π ![0, 0, 1] M := by
  have hp := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero (K := F) hπ
  constructor
  · rintro ⟨hM, u, hu⟩
    have hdet : M.det ≠ 0 := by
      rw [hu]
      exact mul_ne_zero (u.isUnit.map (algebraMap R F)).ne_zero hp
    let g := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet
    obtain ⟨a, ⟨ha, U, V, h⟩, _⟩ := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.gl3_smith_normal_form π hπ g
    have h' : M = U.val.map (algebraMap R F) *
        Matrix.diagonal (fun i => (algebraMap R F π) ^ a i) *
        V.val.map (algebraMap R F) := h
    have hnon : ∀ i, 0 ≤ a i := (integral_diagonal_iff π hπ a).mp
      ((integral_of_factorization_iff U V _ M h').mp hM)
    have hd := factorization_det π hπ a U V M h'
    have he : algebraMap R F (↑(U.det * V.det) : R) *
        (algebraMap R F π) ^ (a 0 + a 1 + a 2) =
        algebraMap R F (u : R) * (algebraMap R F π) ^ (1 : ℤ) := by
      simpa only [zpow_one] using hd.symm.trans hu
    have hs₁ := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.exponent_le_of_unit_coefficient hπ
      (U.det * V.det).isUnit he
    have hs₂ := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.exponent_le_of_unit_coefficient hπ u.isUnit he.symm
    have h01 := ha (show (0 : Fin 3) ≤ 1 by decide)
    have h12 := ha (show (1 : Fin 3) ≤ 2 by decide)
    have hn0 := hnon 0
    have hn1 := hnon 1
    have hn2 := hnon 2
    have heq : a = ![0, 0, 1] := by
      have hc : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 1 := by omega
      ext i
      fin_cases i <;> simp [hc]
    subst a
    exact ⟨U, V, h'⟩
  · rintro ⟨U, V, h⟩
    refine ⟨(integral_of_factorization_iff U V _ M h).mpr ?_, U.det * V.det, ?_⟩
    · apply (integral_diagonal_iff π hπ _).mpr
      intro i
      fin_cases i <;> norm_num
    · simpa using factorization_det π hπ ![0, 0, 1] U V M h

end

/-! Integral permutation matrices reconcile the two choices of dominant order. -/

open scoped BigOperators

def reverseIntegralGL (R : Type*) [CommRing R] : Matrix.GeneralLinearGroup (Fin 3) R where
  val := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  inv := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F]

lemma reverse_conjugation (b : Fin 3 → F) :
    (reverseIntegralGL R).val.map (algebraMap R F) * Matrix.diagonal b *
      (reverseIntegralGL R).val.map (algebraMap R F) = Matrix.diagonal ![b 2, b 1, b 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reverseIntegralGL, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply]

lemma inDoubleCoset_reverse (π : R) (a : Fin 3 → ℤ) (M : CosetCalculusArithmeticMeasure.Mat F)
    (h : InDoubleCoset π a M) : InDoubleCoset π ![a 2, a 1, a 0] M := by
  obtain ⟨U, V, h⟩ := h
  refine ⟨U * reverseIntegralGL R, reverseIntegralGL R * V, ?_⟩
  have hd : (reverseIntegralGL R).val.map (algebraMap R F) *
      Matrix.diagonal (fun i => (algebraMap R F π) ^ (![a 2, a 1, a 0] : Fin 3 → ℤ) i) *
      (reverseIntegralGL R).val.map (algebraMap R F) =
        Matrix.diagonal (fun i => (algebraMap R F π) ^ a i) := by
    rw [reverse_conjugation]
    congr 1
    ext i
    fin_cases i <;> rfl
  change M = (U.val * (reverseIntegralGL R).val).map (algebraMap R F) * _ *
    ((reverseIntegralGL R).val * V.val).map (algebraMap R F)
  rw [Matrix.map_mul, Matrix.map_mul]
  calc
    M = U.val.map (algebraMap R F) *
        Matrix.diagonal (fun i => (algebraMap R F π) ^ a i) * V.val.map (algebraMap R F) := h
    _ = _ := by rw [← hd]; simp only [mul_assoc]

lemma first_doubleCoset_reversal (π : R) (M : CosetCalculusArithmeticMeasure.Mat F) :
    InDoubleCoset π ![1, 0, 0] M ↔ InDoubleCoset π ![0, 0, 1] M := by
  constructor
  · intro h
    exact inDoubleCoset_reverse π ![1, 0, 0] M h
  · intro h
    exact inDoubleCoset_reverse π ![0, 0, 1] M h

end

end OAI.RepresentationTheory.Hecke.DoubleCoset.Calculus
