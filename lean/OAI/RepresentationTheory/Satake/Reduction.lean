import Mathlib

/-! # Reduction -/

namespace OAI.RepresentationTheory.Satake.Reduction.GeneralLinear

noncomputable section

/-! Integral column operations for the GL₃ Iwasawa decomposition. -/

open scoped Classical

open _root_.Matrix ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F]

abbrev O (F : Type*) [Field F] [ValuativeRel F] := (valuation F).integer
abbrev GL3 (R : Type*) [CommRing R] := Matrix.GeneralLinearGroup (Fin 3) R

def integralMap : GL3 (O F) →* GL3 F :=
  Matrix.GeneralLinearGroup.map (valuation F).integer.subtype

def permutation (σ : Equiv.Perm (Fin 3)) : GL3 (O F) :=
  (Matrix.permMatrixHom : Equiv.Perm (Fin 3) →* Matrix (Fin 3) (Fin 3) (O F)).toHomUnits σ

theorem integral_permutation_val (σ : Equiv.Perm (Fin 3)) :
    (integralMap (permutation (F := F) σ)).val = (σ⁻¹).permMatrix F := by
  ext i j
  change (((σ⁻¹).permMatrix (O F) i j : O F) : F) = (σ⁻¹).permMatrix F i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> rfl

theorem mul_permutation_apply (g : GL3 F) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (g * integralMap (permutation (F := F) σ)) i j = g i (σ j) := by
  change (g.val * (integralMap (permutation (F := F) σ)).val) i j = _
  rw [integral_permutation_val]
  change (g.val i ᵥ* (σ⁻¹).permMatrix F) j = _
  rw [Matrix.vecMul_permMatrix]
  rfl

def lowerShear (a b : O F) : GL3 (O F) where
  val := !![1, 0, 0; 0, 1, 0; a, b, 1]
  inv := !![1, 0, 0; 0, 1, 0; -a, -b, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

def middleShear (a : O F) : GL3 (O F) where
  val := !![1, 0, 0; a, 1, 0; 0, 0, 1]
  inv := !![1, 0, 0; -a, 1, 0; 0, 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem mul_lowerShear_apply (g : GL3 F) (a b : O F) (i : Fin 3) :
    (g * integralMap (lowerShear a b)) i 0 = g i 0 + g i 2 * (a : F) ∧
    (g * integralMap (lowerShear a b)) i 1 = g i 1 + g i 2 * (b : F) ∧
    (g * integralMap (lowerShear a b)) i 2 = g i 2 := by
  simp [integralMap, lowerShear, Matrix.mul_apply, Fin.sum_univ_three]

theorem mul_middleShear_apply (g : GL3 F) (a : O F) (i : Fin 3) :
    (g * integralMap (middleShear a)) i 0 = g i 0 + g i 1 * (a : F) ∧
    (g * integralMap (middleShear a)) i 1 = g i 1 ∧
    (g * integralMap (middleShear a)) i 2 = g i 2 := by
  simp [integralMap, middleShear, Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_row_pivot (g : GL3 F) (i : Fin 3) :
    ∃ j : Fin 3, g i j ≠ 0 ∧ ∀ k, valuation F (g i k) ≤ valuation F (g i j) := by
  have hrow : ∃ j : Fin 3, g i j ≠ 0 := by
    by_contra! h
    have hi := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A i i) g.val_inv
    simp [Matrix.mul_apply, h] at hi
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin 3 => valuation F (g i j)) Finset.univ_nonempty
  refine ⟨j, ?_, fun k => hj k (Finset.mem_univ k)⟩
  intro hz
  obtain ⟨k, hk⟩ := hrow
  have h := hj k (Finset.mem_univ k)
  rw [hz, map_zero] at h
  exact hk ((valuation F).zero_iff.mp (le_zero_iff.mp h))

/-- The coefficient for eliminating an entry against a largest-valued pivot
belongs to the valuation ring. -/
def eliminationCoefficient (x p : F) (hp : p ≠ 0)
    (hxp : valuation F x ≤ valuation F p) : O F :=
  ⟨-(x / p), by
    change valuation F (-(x / p)) ≤ 1
    rw [Valuation.map_neg, map_div₀]
    exact (div_le_one₀ ((valuation F).pos_iff.mpr hp)).mpr hxp⟩

theorem eliminate_entry (x p : F) (hp : p ≠ 0)
    (hxp : valuation F x ≤ valuation F p) :
    x + p * (eliminationCoefficient x p hp hxp : F) = 0 := by
  change x + p * (-(x / p)) = 0
  field_simp
  ring

/-- Integral column operations clear the first two entries of the last row. -/
theorem reduce_last_row (g : GL3 F) :
    ∃ U : GL3 (O F),
      (g * integralMap U) 2 0 = 0 ∧
      (g * integralMap U) 2 1 = 0 ∧
      (g * integralMap U) 2 2 ≠ 0 := by
  obtain ⟨j, hj, hmax⟩ := exists_row_pivot g 2
  let P := permutation (F := F) (Equiv.swap j 2)
  let g' := g * integralMap P
  have hp : g' 2 2 ≠ 0 := by
    simpa only [g', P, mul_permutation_apply, Equiv.swap_apply_right] using hj
  have hm (k : Fin 3) : valuation F (g' 2 k) ≤ valuation F (g' 2 2) := by
    simpa only [g', P, mul_permutation_apply, Equiv.swap_apply_right] using
      hmax (Equiv.swap j 2 k)
  let a := eliminationCoefficient (g' 2 0) (g' 2 2) hp (hm 0)
  let b := eliminationCoefficient (g' 2 1) (g' 2 2) hp (hm 1)
  refine ⟨P * lowerShear a b, ?_⟩
  rw [map_mul, ← mul_assoc]
  change (g' * integralMap (lowerShear a b)) 2 0 = 0 ∧
    (g' * integralMap (lowerShear a b)) 2 1 = 0 ∧
    (g' * integralMap (lowerShear a b)) 2 2 ≠ 0
  obtain ⟨h0, h1, h2⟩ := mul_lowerShear_apply g' a b 2
  rw [h0, h1, h2]
  exact ⟨eliminate_entry _ _ hp (hm 0), eliminate_entry _ _ hp (hm 1), hp⟩

/-- The remaining two-dimensional elimination preserves the cleared last row. -/
theorem reduce_second_row (g : GL3 F) (h20 : g 2 0 = 0) (h21 : g 2 1 = 0) :
    ∃ U : GL3 (O F),
      (g * integralMap U) 1 0 = 0 ∧
      (g * integralMap U) 2 0 = 0 ∧
      (g * integralMap U) 2 1 = 0 := by
  have hpair : ∃ k ∈ ({0, 1} : Finset (Fin 3)), g 1 k ≠ 0 := by
    by_contra! h
    have h10 := h 0 (by simp)
    have h11 := h 1 (by simp)
    apply g.det_ne_zero
    simp [Matrix.det_fin_three, h20, h21, h10, h11]
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image ({0, 1} : Finset (Fin 3))
    (fun j => valuation F (g 1 j)) (by simp)
  have hj01 : j = 0 ∨ j = 1 := by simpa using hj
  have hjnz : g 1 j ≠ 0 := by
    intro hz
    obtain ⟨k, hk, hknz⟩ := hpair
    have h := hmax k hk
    rw [hz, map_zero] at h
    exact hknz ((valuation F).zero_iff.mp (le_zero_iff.mp h))
  let P := permutation (F := F) (Equiv.swap j 1)
  let g' := g * integralMap P
  have hp : g' 1 1 ≠ 0 := by
    simpa only [g', P, mul_permutation_apply, Equiv.swap_apply_right] using hjnz
  have hm : valuation F (g' 1 0) ≤ valuation F (g' 1 1) := by
    have hmem : Equiv.swap j 1 0 ∈ ({0, 1} : Finset (Fin 3)) := by
      rcases hj01 with rfl | rfl <;> simp
    simpa only [g', P, mul_permutation_apply, Equiv.swap_apply_right] using
      hmax (Equiv.swap j 1 0) hmem
  have hg20 : g' 2 0 = 0 := by
    change (g * integralMap (permutation (F := F) (Equiv.swap j 1))) 2 0 = 0
    rw [mul_permutation_apply]
    rcases hj01 with rfl | rfl <;> simp [h20, h21]
  have hg21 : g' 2 1 = 0 := by
    change (g * integralMap (permutation (F := F) (Equiv.swap j 1))) 2 1 = 0
    rw [mul_permutation_apply, Equiv.swap_apply_right]
    rcases hj01 with rfl | rfl
    · exact h20
    · exact h21
  let a := eliminationCoefficient (g' 1 0) (g' 1 1) hp hm
  refine ⟨P * middleShear a, ?_⟩
  rw [map_mul, ← mul_assoc]
  change (g' * integralMap (middleShear a)) 1 0 = 0 ∧
    (g' * integralMap (middleShear a)) 2 0 = 0 ∧
    (g' * integralMap (middleShear a)) 2 1 = 0
  obtain ⟨h10, _, _⟩ := mul_middleShear_apply g' a 1
  obtain ⟨h20', h21', _⟩ := mul_middleShear_apply g' a 2
  rw [h10, h20', h21', hg20, hg21]
  exact ⟨eliminate_entry _ _ hp hm, by simp, rfl⟩

omit [ValuativeRel F] in
theorem upperTriangular_of_below_zero (g : GL3 F)
    (h10 : g 1 0 = 0) (h20 : g 2 0 = 0) (h21 : g 2 1 = 0) :
    g.val.IsUpperTriangular := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- GL₃ over a valued field admits an upper-triangular representative
after right multiplication by an invertible integral matrix. -/
theorem exists_integral_upperTriangular (g : GL3 F) :
    ∃ U : GL3 (O F), (g * integralMap U).val.IsUpperTriangular := by
  obtain ⟨U, h20, h21, _⟩ := reduce_last_row g
  obtain ⟨V, h10', h20', h21'⟩ := reduce_second_row (g * integralMap U) h20 h21
  refine ⟨U * V, ?_⟩
  rw [map_mul, ← mul_assoc]
  exact upperTriangular_of_below_zero _ h10' h20' h21'

end

end OAI.RepresentationTheory.Satake.Reduction.GeneralLinear
