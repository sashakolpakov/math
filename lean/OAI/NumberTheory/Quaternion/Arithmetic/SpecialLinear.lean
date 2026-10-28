import OAI.NumberTheory.Quaternion.Arithmetic.FiniteIndex

/-! # Special Linear -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SpecialLinear

noncomputable section

section

/-! Elementary generation and exclusion of finite-index subgroups for the
split special-linear groups occurring in the local approximation argument. -/

open scoped Classical
open _root_.Matrix _root_.Matrix.SpecialLinearGroup

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem diagonal_pair_transvection_decomposition {i j : ι} (hij : i ≠ j)
    (a : K) (ha : a ≠ 0) :
    diag2n hij a ha =
      transvection hij a * transvection hij.symm (-a⁻¹) * transvection hij a *
      transvection hij (-1) * transvection hij.symm 1 * transvection hij (-1) := by
  apply Subtype.ext
  change Matrix.diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1) =
    Matrix.transvection i j a * Matrix.transvection j i (-a⁻¹) * Matrix.transvection i j a *
    Matrix.transvection i j (-1) * Matrix.transvection j i 1 * Matrix.transvection i j (-1)
  simp only [Matrix.mul_assoc]
  apply Matrix.ext
  intro r s
  simp only [Matrix.diagonal_apply]
  by_cases hri : r = i
  · subst r
    simp only [transvection_mul_apply_same, transvection_mul_apply_of_ne j i i s hij,
      transvection_mul_apply_of_ne i j j s hij.symm]
    by_cases hsi : s = i <;> by_cases hsj : s = j <;>
      simp_all [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, eq_comm]
  · by_cases hrj : r = j
    · subst r
      simp only [transvection_mul_apply_same, transvection_mul_apply_of_ne j i i s hij,
        transvection_mul_apply_of_ne i j j s hij.symm]
      by_cases hsi : s = i <;> by_cases hsj : s = j <;>
        simp_all [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, eq_comm]
    · simp only [transvection_mul_apply_of_ne i j r s hri,
        transvection_mul_apply_of_ne j i r s hrj]
      by_cases hrs : r = s
      · subst s
        simp_all [Matrix.transvection, eq_comm]
      · simp_all [Matrix.transvection, eq_comm]

theorem specialLinear_transvection_induction [Nontrivial ι]
    (P : Matrix.SpecialLinearGroup ι K → Prop)
    (ht : ∀ (i j : ι) (hij : i ≠ j) (a : K), P (transvection hij a))
    (hm : ∀ g h, P g → P h → P (g * h)) (g : Matrix.SpecialLinearGroup ι K) : P g := by
  apply diagonal_transvection_induction' P g _ ht hm
  intro i j hij a ha
  rw [diagonal_pair_transvection_decomposition hij a ha]
  exact hm _ _ (hm _ _ (hm _ _ (hm _ _ (hm _ _
    (ht i j hij a) (ht j i hij.symm (-a⁻¹))) (ht i j hij a))
    (ht i j hij (-1))) (ht j i hij.symm 1)) (ht i j hij (-1))

theorem specialLinear_finiteIndex_eq_top [CharZero K] [Nontrivial ι]
    (H : Subgroup (Matrix.SpecialLinearGroup ι K)) [H.FiniteIndex] : H = ⊤ := by
  apply top_unique
  intro g _
  exact specialLinear_transvection_induction (fun g => g ∈ H)
    (fun _ _ hij a => Arithmetic.FiniteIndex.transvection_mem_finiteIndex H hij a)
    (fun _ _ ha hb => H.mul_mem ha hb) g

end

/-! A homomorphism out of SL takes its values in a subgroup once
the images of elementary transvections do. -/

open scoped Classical

theorem specialLinear_hom_mem_of_transvections {K H : Type*} [Field K] [Group H]
    {n : ℕ} [Nontrivial (Fin n)] (f : Matrix.SpecialLinearGroup (Fin n) K →* H)
    (C : Subgroup H)
    (htrans : ∀ (i j : Fin n) (hij : i ≠ j) (t : K),
      f (Matrix.SpecialLinearGroup.transvection hij t) ∈ C)
    (g : Matrix.SpecialLinearGroup (Fin n) K) : f g ∈ C := by
  apply specialLinear_transvection_induction (fun g => f g ∈ C)
  · exact htrans
  · intro g h hg hh
    rw [map_mul]
    exact C.mul_mem hg hh

end

end OAI.NumberTheory.Quaternion.Arithmetic.SpecialLinear
