import OAI.RepresentationTheory.Hecke.DoubleCoset

/-! # Dual -/

namespace OAI.RepresentationTheory.Hecke.Dual.CosetCalculus

noncomputable section

section

/-! Inverse matrices identify the second minuscule coset with the first. -/

open scoped BigOperators

variable {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

def dualMatrix (p : F) (M : CosetCalculusArithmeticMeasure.Mat F) : CosetCalculusArithmeticMeasure.Mat F := p • M⁻¹

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
lemma map_integralGL_inverse (U : Matrix.GeneralLinearGroup (Fin 3) R) :
    (U.val.map (algebraMap R F))⁻¹ = U⁻¹.val.map (algebraMap R F) := by
  change (Matrix.GeneralLinearGroup.map (algebraMap R F) U).val⁻¹ = _
  rw [← Matrix.GeneralLinearGroup.coe_inv, ← map_inv]
  rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
lemma dual_factorization (p : F)
    (U V : Matrix.GeneralLinearGroup (Fin 3) R) (D M : CosetCalculusArithmeticMeasure.Mat F)
    (h : M = U.val.map (algebraMap R F) * D * V.val.map (algebraMap R F)) :
    dualMatrix p M = V⁻¹.val.map (algebraMap R F) * dualMatrix p D *
      U⁻¹.val.map (algebraMap R F) := by
  rw [dualMatrix, h, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    map_integralGL_inverse, map_integralGL_inverse]
  simp only [dualMatrix, Matrix.mul_smul, Matrix.smul_mul, mul_assoc]

lemma dual_diagonal (p : F) (hp : p ≠ 0) (a : Fin 3 → ℤ) :
    dualMatrix p (Matrix.diagonal (fun i => p ^ a i)) =
      Matrix.diagonal (fun i => p ^ (1 - a i)) := by
  have hi : (Matrix.diagonal (fun i => p ^ a i))⁻¹ =
      Matrix.diagonal (fun i => (p ^ a i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [zpow_ne_zero _ hp]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [dualMatrix, hi, ← Matrix.diagonal_smul]
  congr 1
  ext i
  simp [zpow_sub₀ hp, div_eq_mul_inv]

lemma dualMatrix_involutive (p : F) (hp : p ≠ 0) (M : CosetCalculusArithmeticMeasure.Mat F) (hM : M.det ≠ 0) :
    dualMatrix p (dualMatrix p M) = M := by
  let := invertibleOfNonzero hp
  let := Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hM)
  rw [dualMatrix, dualMatrix, Matrix.inv_smul M⁻¹ p (Matrix.isUnit_det_of_invertible _),
    Matrix.inv_inv_of_invertible, smul_smul, mul_invOf_self, one_smul]

lemma triangular_inverse (p : F) (hp : p ≠ 0) (a : Fin 3 → ℤ) (x y z : F) :
    (CosetCalculusArithmeticMeasure.triangular p a x y z)⁻¹ =
      !![(p ^ a 0)⁻¹, -x * (p ^ a 1)⁻¹, (x * z - y) * (p ^ a 2)⁻¹;
         0, (p ^ a 1)⁻¹, -z * (p ^ a 2)⁻¹;
         0, 0, (p ^ a 2)⁻¹] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CosetCalculusArithmeticMeasure.triangular, Matrix.mul_apply, Fin.sum_univ_succ, zpow_ne_zero _ hp]
  all_goals field_simp
  all_goals ring

lemma dual_triangular (p : F) (hp : p ≠ 0) (a : Fin 3 → ℤ) (x y z : F) :
    dualMatrix p (CosetCalculusArithmeticMeasure.triangular p a x y z) =
      !![p ^ (1 - a 0), -x * p ^ (1 - a 1), (x * z - y) * p ^ (1 - a 2);
         0, p ^ (1 - a 1), -z * p ^ (1 - a 2);
         0, 0, p ^ (1 - a 2)] := by
  rw [dualMatrix, triangular_inverse p hp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, zpow_sub₀ hp, div_eq_mul_inv, mul_left_comm]

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem dual_doubleCoset (π : R) (hπ : Irreducible π) (a : Fin 3 → ℤ) (M : CosetCalculusArithmeticMeasure.Mat F)
    (hM : M.det ≠ 0) :
    DoubleCoset.Calculus.InDoubleCoset π a M ↔
      DoubleCoset.Calculus.InDoubleCoset π (fun i => 1 - a i) (dualMatrix (algebraMap R F π) M) := by
  have hp := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero (K := F) hπ
  constructor
  · rintro ⟨U, V, h⟩
    refine ⟨V⁻¹, U⁻¹, ?_⟩
    rw [dual_factorization _ U V _ M h, dual_diagonal _ hp]
  · rintro ⟨U, V, h⟩
    refine ⟨V⁻¹, U⁻¹, ?_⟩
    have hh := dual_factorization (algebraMap R F π) U V _ _ h
    rw [dualMatrix_involutive _ hp M hM, dual_diagonal _ hp] at hh
    simpa only [sub_sub_cancel] using hh

end

/-! The unipotent sections of the two minuscule double cosets. -/

variable {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
@[simp] lemma integralElement_neg (x : F) :
    CosetCalculusArithmeticMeasure.IntegralElement (R := R) (-x) ↔ CosetCalculusArithmeticMeasure.IntegralElement (R := R) x :=
  (algebraMap R F).range.neg_mem_iff

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma firstCondition_triangular (π : R) (hπ : Irreducible π)
    (a : Fin 3 → ℤ) (x y z : F) :
    DoubleCoset.Calculus.FirstCondition π (CosetCalculusArithmeticMeasure.triangular (algebraMap R F π) a x y z) ↔
      (a = ![1, 0, 0] ∨ a = ![0, 1, 0] ∨ a = ![0, 0, 1]) ∧
      CosetCalculusArithmeticMeasure.IntegralElement (R := R) ((algebraMap R F π) ^ a 0 * x) ∧
      CosetCalculusArithmeticMeasure.IntegralElement (R := R) ((algebraMap R F π) ^ a 0 * y) ∧
      CosetCalculusArithmeticMeasure.IntegralElement (R := R) ((algebraMap R F π) ^ a 1 * z) := by
  have hp := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero (K := F) hπ
  have hd : (∃ u : Rˣ, (algebraMap R F π) ^ (a 0 + a 1 + a 2) =
      algebraMap R F (u : R) * algebraMap R F π) ↔ a 0 + a 1 + a 2 = 1 := by
    simpa only [zpow_one] using CosetCalculusArithmeticMeasure.zpow_eq_unit_mul_iff (F := F) π hπ (a 0 + a 1 + a 2) 1
  rw [DoubleCoset.Calculus.FirstCondition, CosetCalculusArithmeticMeasure.triangular_integral, CosetCalculusArithmeticMeasure.triangular_det _ hp, hd,
    CosetCalculusArithmeticMeasure.integral_zpow π hπ, CosetCalculusArithmeticMeasure.integral_zpow π hπ, CosetCalculusArithmeticMeasure.integral_zpow π hπ]
  constructor
  · rintro ⟨⟨h0, h1, h2, hx, hy, hz⟩, hs⟩
    refine ⟨CosetCalculusArithmeticMeasure.nonnegative_triple_sum_one a ?_ hs, hx, hy, hz⟩
    intro i
    fin_cases i <;> assumption
  · rintro ⟨ha, hx, hy, hz⟩
    rcases ha with rfl | rfl | rfl <;> simp_all

lemma dual_triangular_det (p : F) (hp : p ≠ 0) (a : Fin 3 → ℤ) (x y z : F) :
    (dualMatrix p (CosetCalculusArithmeticMeasure.triangular p a x y z)).det = p ^ (3 - (a 0 + a 1 + a 2)) := by
  rw [dual_triangular p hp]
  have he : 3 - (a 0 + a 1 + a 2) = (1 - a 0) + (1 - a 1) + (1 - a 2) := by ring
  simp [Matrix.det_fin_three, he, zpow_add₀ hp, mul_assoc]

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma dual_triangular_integral (π : R) (hπ : Irreducible π)
    (a : Fin 3 → ℤ) (x y z : F) :
    CosetCalculusArithmeticMeasure.IntegralMatrix (R := R) (dualMatrix (algebraMap R F π)
      (CosetCalculusArithmeticMeasure.triangular (algebraMap R F π) a x y z)) ↔
      (∀ i, a i ≤ 1) ∧
      CosetCalculusArithmeticMeasure.IntegralElement (R := R) ((algebraMap R F π) ^ (1 - a 1) * x) ∧
      CosetCalculusArithmeticMeasure.IntegralElement (R := R) ((algebraMap R F π) ^ (1 - a 2) * (x * z - y)) ∧
      CosetCalculusArithmeticMeasure.IntegralElement (R := R) ((algebraMap R F π) ^ (1 - a 2) * z) := by
  have hp := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero (K := F) hπ
  rw [CosetCalculusArithmeticMeasure.integralMatrix_iff, dual_triangular _ hp]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      have hid : CosetCalculusArithmeticMeasure.IntegralElement (R := R) ((algebraMap R F π) ^ (1 - a i)) := by
        fin_cases i
        · exact h 0 0
        · exact h 1 1
        · exact h 2 2
      have hi : 0 ≤ 1 - a i := (CosetCalculusArithmeticMeasure.integral_zpow π hπ _).mp hid
      omega
    · have hh : CosetCalculusArithmeticMeasure.IntegralElement (R := R) (-x * (algebraMap R F π) ^ (1 - a 1)) := h 0 1
      simpa only [neg_mul, integralElement_neg, mul_comm] using hh
    · have hh : CosetCalculusArithmeticMeasure.IntegralElement (R := R) ((x * z - y) * (algebraMap R F π) ^ (1 - a 2)) := h 0 2
      simpa only [mul_comm] using hh
    · have hh : CosetCalculusArithmeticMeasure.IntegralElement (R := R) (-z * (algebraMap R F π) ^ (1 - a 2)) := h 1 2
      simpa only [neg_mul, integralElement_neg, mul_comm] using hh
  · rintro ⟨ha, hx, hy, hz⟩ i j
    have hd (i : Fin 3) : CosetCalculusArithmeticMeasure.IntegralElement (R := R) ((algebraMap R F π) ^ (1 - a i)) :=
      (CosetCalculusArithmeticMeasure.integral_zpow π hπ _).mpr (by have := ha i; omega)
    have hx' : CosetCalculusArithmeticMeasure.IntegralElement (R := R) (-x * (algebraMap R F π) ^ (1 - a 1)) := by
      simpa only [neg_mul, integralElement_neg, mul_comm] using hx
    have hy' : CosetCalculusArithmeticMeasure.IntegralElement (R := R) ((x * z - y) * (algebraMap R F π) ^ (1 - a 2)) := by
      simpa only [mul_comm] using hy
    have hz' : CosetCalculusArithmeticMeasure.IntegralElement (R := R) (-z * (algebraMap R F π) ^ (1 - a 2)) := by
      simpa only [neg_mul, integralElement_neg, mul_comm] using hz
    fin_cases i <;> fin_cases j
    all_goals first
      | exact hd 0
      | exact hd 1
      | exact hd 2
      | exact hx'
      | exact hy'
      | exact hz'
      | exact ⟨0, map_zero _⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma secondCondition_triangular (π : R) (hπ : Irreducible π)
    (a : Fin 3 → ℤ) (x y z : F) :
    DoubleCoset.Calculus.FirstCondition π (dualMatrix (algebraMap R F π)
      (CosetCalculusArithmeticMeasure.triangular (algebraMap R F π) a x y z)) ↔
      (a = ![1, 1, 0] ∨ a = ![1, 0, 1] ∨ a = ![0, 1, 1]) ∧
      CosetCalculusArithmeticMeasure.IntegralElement (R := R) ((algebraMap R F π) ^ (1 - a 1) * x) ∧
      CosetCalculusArithmeticMeasure.IntegralElement (R := R) ((algebraMap R F π) ^ (1 - a 2) * (x * z - y)) ∧
      CosetCalculusArithmeticMeasure.IntegralElement (R := R) ((algebraMap R F π) ^ (1 - a 2) * z) := by
  have hp := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero (K := F) hπ
  have hd : (∃ u : Rˣ, (algebraMap R F π) ^ (3 - (a 0 + a 1 + a 2)) =
      algebraMap R F (u : R) * algebraMap R F π) ↔ 3 - (a 0 + a 1 + a 2) = 1 := by
    simpa only [zpow_one] using CosetCalculusArithmeticMeasure.zpow_eq_unit_mul_iff (F := F) π hπ (3 - (a 0 + a 1 + a 2)) 1
  rw [DoubleCoset.Calculus.FirstCondition, dual_triangular_integral π hπ, dual_triangular_det _ hp, hd]
  constructor
  · rintro ⟨⟨ha, hx, hy, hz⟩, hs⟩
    exact ⟨CosetCalculusArithmeticMeasure.bounded_triple_sum_two a ha (by omega), hx, hy, hz⟩
  · rintro ⟨ha, hx, hy, hz⟩
    rcases ha with rfl | rfl | rfl <;> simp_all [Fin.forall_fin_succ]

end

end OAI.RepresentationTheory.Hecke.Dual.CosetCalculus
