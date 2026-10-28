import Mathlib

/-! # Pivots -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Pivots.CM

noncomputable section

/-! Unit pivots for elementary reduction of integral SL3. These use
the local-ring axiom and the actual inverse matrix, without passage to
the fraction field or a generation hypothesis. -/

open scoped Classical _root_.Matrix
open _root_.Matrix _root_.Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem column_has_unit (g : SpecialLinearGroup (Fin 3) R) (j : Fin 3) :
    ∃ i : Fin 3, IsUnit (g.val i j) := by
  have hsum : IsUnit (∑ i : Fin 3, (g⁻¹).val j i * g.val i j) := by
    change IsUnit ((g⁻¹ * g).val j j)
    rw [inv_mul_cancel]
    simpa only [coe_one, Matrix.one_apply_eq] using (isUnit_one : IsUnit (1 : R))
  obtain ⟨i, _, hi⟩ := IsLocalRing.exists_of_isUnit_sum hsum
  exact ⟨i, isUnit_of_mul_isUnit_right hi⟩

omit [IsLocalRing R] in
theorem row_add (g : SpecialLinearGroup (Fin 3) R) (i j : Fin 3) (hij : i ≠ j)
    (a : R) (r c : Fin 3) :
    (transvection hij a * g).val r c =
      g.val r c + if r = i then a * g.val j c else 0 := by
  change ((1 + single i j a) * g.val) r c = _
  rw [add_mul, Matrix.one_mul, Matrix.add_apply]
  congr 1
  by_cases h : r = i
  · subst r
    simp only [Matrix.single_mul_apply_same, ite_true]
  · rw [ite_eq_right h]
    exact Matrix.single_mul_apply_of_ne a i j r c h g.val

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Pivots.CM
