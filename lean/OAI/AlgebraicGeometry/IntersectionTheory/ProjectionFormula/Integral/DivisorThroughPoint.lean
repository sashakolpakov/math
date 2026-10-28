import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Divisor Through Point -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.DivisorThroughPoint

noncomputable section

/-! Every nongeneric point of an integral noetherian scheme lies on
an actual codimension-one closed integral subscheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order IsLocalRing

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem exists_support (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : x ≠ genericPoint X) :
    ∃ W : IrreducibleCloseds X, coheight (CycleClass.Thom.IntersectionGeometry.supportPoint W) = 1 ∧ x ∈ (W : Set X) := by
  let R := X.presheaf.stalk x
  have hlt : x < genericPoint X := lt_of_le_not_ge (genericPoint_specializes x) (by
    intro h
    exact hx (Specializes.antisymm h (genericPoint_specializes x)).eq)
  have hlo : 1 ≤ coheight x := by
    have h := coheight_add_one_le hlt
    have hη : coheight (genericPoint X) = 0 := (isTop_top : IsTop (⊤ : X)).isMax.coheight_eq_zero
    simpa only [hη, zero_add] using h
  have hm : maximalIdeal R ≠ ⊥ := by
    intro he
    have hh : (maximalIdeal R).height = 0 := by rw [he]; simp
    have hz : coheight x = 0 := by
      apply WithBot.coe_injective
      rw [← ringKrullDim_stalk_eq_coheight, ← maximalIdeal_height_eq_ringKrullDim, hh]
    rw [hz] at hlo
    norm_num at hlo
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨p, hp, _⟩ := Ideal.exists_minimalPrimes_le
    (show Ideal.span {r} ≤ maximalIdeal R from Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hr))
  let : p.IsPrime := hp.isPrime
  have hrp : r ∈ p := hp.le (Ideal.subset_span (Set.mem_singleton r))
  have hp0 : p ≠ ⊥ := fun he => hr0 (by simpa only [he, Submodule.mem_bot] using hrp)
  have hh : p.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {r}) p hp)
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hp0))
  let q : Spec R := ⟨p, hp.isPrime⟩
  refine ⟨Stalk.DivisorSupport.primeClosure X x q, ?_, Stalk.DivisorSupport.point_mem_primeClosure X x q⟩
  rw [Stalk.DivisorSupport.primeClosure_point, ← Stalk.Localization.height_eq_coheight_image]
  exact hh

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.DivisorThroughPoint
