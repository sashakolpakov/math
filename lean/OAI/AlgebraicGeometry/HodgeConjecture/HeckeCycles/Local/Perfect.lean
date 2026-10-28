import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Reduction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RingCommutators

/-! # Perfect -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Perfect.CM

noncomputable section

/-! Elementary generation and perfectness of SL3 over a local ring,
proved by unit-pivot row reduction in that same ring. -/

open scoped Classical _root_.Matrix
open _root_.Matrix _root_.Matrix.SpecialLinearGroup
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Pivots.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Reduction.CM

variable {R : Type*} [CommRing R]

theorem upper_word (g : SpecialLinearGroup (Fin 3) R)
    (h00 : g.val 0 0 = 1) (h11 : g.val 1 1 = 1) (h22 : g.val 2 2 = 1)
    (h10 : g.val 1 0 = 0) (h20 : g.val 2 0 = 0) (h21 : g.val 2 1 = 0) :
    g = transvection (show (0 : Fin 3) ≠ 1 by decide) (g.val 0 1) *
      transvection (show (0 : Fin 3) ≠ 2 by decide) (g.val 0 2 - g.val 0 1 * g.val 1 2) *
      transvection (show (1 : Fin 3) ≠ 2 by decide) (g.val 1 2) := by
  apply Subtype.ext
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp_all [mul_assoc, Pivots.CM.row_add, transvection_coe, Matrix.single]

variable [IsLocalRing R]

theorem subgroup_eq_top (S : Subgroup (SpecialLinearGroup (Fin 3) R))
    (hS : ∀ (i j : Fin 3) (hij : i ≠ j) (a : R), SpecialLinearGroup.transvection hij a ∈ S) : S = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨A, hA, h00, h10, h20, h11, h21⟩ := Reduction.CM.first_two_columns S hS g
  have h22 : (A * g).val 2 2 = 1 := by
    have hdet := (A * g).property
    rw [Matrix.det_fin_three] at hdet
    simpa only [h00, h10, h20, h11, h21, one_mul, mul_one, mul_zero, zero_mul,
      add_zero, zero_add, sub_zero] using hdet
  have hB : A * g ∈ S := by
    rw [upper_word (A * g) h00 h11 h22 h10 h20 h21]
    exact S.mul_mem (S.mul_mem (hS _ _ _ _) (hS _ _ _ _)) (hS _ _ _ _)
  have h := S.mul_mem (S.inv_mem hA) hB
  simpa only [inv_mul_cancel_left] using h

theorem commutator_eq_top : commutator (SpecialLinearGroup (Fin 3) R) = ⊤ :=
  subgroup_eq_top _ (RingCommutators.CM.elementary_mem_commutator)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Perfect.CM
