import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorIdealEq
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Ideal.Maps

/-! # Denominator Base -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorBase.Construction.DenominatorBaseChange

/-! Denominator ideals commute with flat extension inside a common fraction field. -/

variable {R S F : Type*} [CommRing R] [CommRing S] [Field F]
variable [IsDomain R] [IsDomain S] [Algebra R S] [Algebra R F] [Algebra S F]
variable [IsScalarTower R S F] [IsFractionRing R F] [IsFractionRing S F] [Module.Flat R S]

omit [IsDomain S] in
theorem map (x : F) :
    (DenominatorIdealEq.Construction.DenominatorIdeal.ideal (R := R) x).map (algebraMap R S) =
      DenominatorIdealEq.Construction.DenominatorIdeal.ideal (R := S) x := by
  classical
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro r ⟨s, hs⟩
    refine ⟨algebraMap R S s, ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply R S F] using hs
  obtain ⟨a, b, hab⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) x
  have hb : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hx : x = algebraMap R F a / algebraMap R F b := by
    rw [← hab, IsFractionRing.mk'_eq_div]
  have hbS : algebraMap R S b ≠ 0 := by
    intro h
    apply hb
    apply IsFractionRing.injective R F
    rw [map_zero, IsScalarTower.algebraMap_apply R S F, h, map_zero]
  have hxS : x = algebraMap S F (algebraMap R S a) /
      algebraMap S F (algebraMap R S b) := by
    simpa only [← IsScalarTower.algebraMap_apply R S F] using hx
  intro r hr
  obtain ⟨s, hs⟩ := (DenominatorIdealEq.Construction.DenominatorIdeal.mem_iff_dvd _ _ r hbS hxS).mp hr
  have hrel : ∑ i : Fin 2, (![a, -(b : R)] i) • (![r, s] i) = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Algebra.smul_def, map_neg, neg_mul, ← sub_eq_add_neg, sub_eq_zero]
    exact hs
  obtain ⟨k, c, y, hxy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  have h0 : r = ∑ j, algebraMap R S (c 0 j) * y j := by
    simpa only [Algebra.smul_def, Matrix.cons_val_zero] using hxy 0
  rw [h0]
  apply Submodule.sum_mem
  intro j _
  apply Ideal.mul_mem_right
  apply Ideal.mem_map_of_mem
  apply (DenominatorIdealEq.Construction.DenominatorIdeal.mem_iff_dvd a b (c 0 j) hb hx).mpr
  refine ⟨c 1 j, ?_⟩
  have h := hc j
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    neg_mul, ← sub_eq_add_neg, sub_eq_zero] using h

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorBase.Construction.DenominatorBaseChange
