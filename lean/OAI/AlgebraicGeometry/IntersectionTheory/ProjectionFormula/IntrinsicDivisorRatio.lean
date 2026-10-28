import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicDivisorEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.DivisorInverse

/-! # Intrinsic Divisor Ratio -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicDivisorRatio

noncomputable section

/-! The native local divisor intersection formula for a ratio whose
numerator and denominator both restrict nontrivially to the divisor. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Intrinsic

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem ord_div (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (f g : X.functionField) (hf : f ≠ 0) (hg : g ≠ 0) (x : X) :
    X.ord (f / g) x = X.ord f x - X.ord g x := by
  rw [div_eq_mul_inv, Scheme.ord_mul hf (inv_ne_zero hg), Principal.DivisorInverse.ord_inv,
    sub_eq_add_neg]

theorem order_ratio_eq_sum (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport 1) (C : X.DimensionCycleSupport 2)
    (hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (a b : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
    (ha : Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx a ≠ 0)
    (hb : Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx b ≠ 0) :
    let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val
    let y := CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
    let f := algebraMap R X.carrier.functionField a / algebraMap R X.carrier.functionField b
    let g := algebraMap (Y.presheaf.stalk y) Y.functionField
        (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx a) /
      algebraMap (Y.presheaf.stalk y) Y.functionField
        (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx b)
    ∃ S : Finset (Spec R),
      (∀ p ∈ S, p.asIdeal.height = 1 ∧
        X.supportCodimension (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) = 1) ∧
      (∀ p : Spec R, p.asIdeal.height = 1 → p ∉ S →
        X.carrier.ord f (X.carrier.fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) = 0) ∧
      (Y.ord g y : ℚ) = ∑ p ∈ S,
        (X.carrier.ord f (X.carrier.fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) : ℚ) *
          CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) A.val C.val := by
  let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
  let σ := Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
  let fa := algebraMap R X.carrier.functionField a
  let fb := algebraMap R X.carrier.functionField b
  let ga := algebraMap (Y.presheaf.stalk y) Y.functionField (σ a)
  let gb := algebraMap (Y.presheaf.stalk y) Y.functionField (σ b)
  have ha0 : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  have hb0 : b ≠ 0 := fun h => hb (by rw [h, map_zero])
  have hfa : fa ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R X.carrier.functionField)).mpr ha0
  have hfb : fb ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R X.carrier.functionField)).mpr hb0
  have hga : ga ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField)).mpr ha
  have hgb : gb ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField)).mpr hb
  obtain ⟨Sa, hSa, hoa, hea⟩ := IntrinsicDivisorEuler.Intrinsic.order_restriction_eq_sum X m A C hx a ha
  obtain ⟨Sb, hSb, hob, heb⟩ := IntrinsicDivisorEuler.Intrinsic.order_restriction_eq_sum X m A C hx b hb
  let S := Sa ∪ Sb
  have hS (p : Spec R) (hp : p ∈ S) : p.asIdeal.height = 1 ∧
      X.supportCodimension (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) = 1 := by
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ⟨(hSa p hp).1, (hSa p hp).2.2⟩
    · exact ⟨(hSb p hp).1, (hSb p hp).2.2⟩
  refine ⟨S, hS, ?_, ?_⟩
  · intro p hp hpS
    rw [ord_div X.carrier fa fb hfa hfb,
      hoa p hp (fun h => hpS (Finset.mem_union_left _ h)),
      hob p hp (fun h => hpS (Finset.mem_union_right _ h)), sub_self]
  · have hea' : (Y.ord ga y : ℚ) = ∑ p ∈ S,
        (X.carrier.ord fa (X.carrier.fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) : ℚ) *
          CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) A.val C.val := by
      rw [hea]
      apply Finset.sum_subset Finset.subset_union_left
      intro p hp hpSa
      rw [hoa p (hS p hp).1 hpSa, Int.cast_zero, zero_mul]
    have heb' : (Y.ord gb y : ℚ) = ∑ p ∈ S,
        (X.carrier.ord fb (X.carrier.fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) : ℚ) *
          CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) A.val C.val := by
      rw [heb]
      apply Finset.sum_subset Finset.subset_union_right
      intro p hp hpSb
      rw [hob p (hS p hp).1 hpSb, Int.cast_zero, zero_mul]
    rw [ord_div Y ga gb hga hgb, Int.cast_sub, hea', heb', ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [ord_div X.carrier fa fb hfa hfb, Int.cast_sub, sub_mul]

end Intrinsic

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicDivisorRatio
