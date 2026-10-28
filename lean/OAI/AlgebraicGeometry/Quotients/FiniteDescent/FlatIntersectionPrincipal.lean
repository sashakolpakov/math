import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Ideal.Maps

/-! # Flat Intersection Principal -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatIntersectionPrincipal.Construction.FlatIntersection

/-! Flat extension preserves intersections of two principal ideals. -/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

theorem principal (a b : R) :
    (Ideal.span {a} ⊓ Ideal.span {b}).map (algebraMap R S) =
      Ideal.span {algebraMap R S a} ⊓ Ideal.span {algebraMap R S b} := by
  classical
  apply le_antisymm
  · simpa [Ideal.map_span] using
      (Ideal.map_inf_le (algebraMap R S) (I := Ideal.span {a}) (J := Ideal.span {b}))
  intro x hx
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hx.1
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hx.2
  have hrel : ∑ i : Fin 2, (![a, -b] i) • (![u, v] i) = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Algebra.smul_def, map_neg, neg_mul, ← hu, ← hv, add_neg_cancel]
  obtain ⟨k, c, y, hxy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  have h0 : u = ∑ j, c 0 j • y j := hxy 0
  have he : x = ∑ j, algebraMap R S (a * c 0 j) * y j := by
    rw [hu, h0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Algebra.smul_def, map_mul, mul_assoc]
  rw [he]
  apply Submodule.sum_mem
  intro j _
  apply Ideal.mul_mem_right
  apply Ideal.mem_map_of_mem
  constructor
  · exact Ideal.mem_span_singleton.mpr ⟨c 0 j, rfl⟩
  · have hj : a * c 0 j = b * c 1 j := by
      have h := hc j
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        neg_mul, ← sub_eq_add_neg, sub_eq_zero] using h
    exact Ideal.mem_span_singleton.mpr ⟨c 1 j, hj⟩

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatIntersectionPrincipal.Construction.FlatIntersection
