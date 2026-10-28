import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedSupportRelation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.NestedPrimeComparison
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.StalkRatioOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.FractionIdentity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.SupportSurfaceStalk

/-! # Restricted Support Coefficient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedSupportCoefficient

noncomputable section

section

/-! Coefficients of the constructed principal relation are the exact
local numerator-minus-denominator orders in the surface prime quotients. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedSupportRelation

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport k) (hDW : ¬ W.val ≤ D.val)
  (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField)
  (hunit : ∀ y : CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val, Order.coheight y = 1 →
    CycleClass.Geometric.GenericPoint.reducedSupportι W.val y ∈ (D.val : Set X.carrier) →
      ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y, IsUnit u ∧
        algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y)
          (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = g)
  (A : X.DimensionCycleSupport (1 + k)) (hA : A ∈ (Divisor.SupportCycle.cycle X m k D W).support)
  (C : X.DimensionCycleSupport (1 + (k + 1))) (hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W.val : Set X.carrier))

include hxW in
theorem zero_outside (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∉ (A.val : Set X.carrier)) :
    RestrictedSupportRelation.term X m k D W hDW g hunit A hA C = 0 := by
  let hAW := (Divisor.SupportCycle.support_subset X m k D W hDW A hA).2
  have hn : CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW ∉
      (RestrictedSupportRelation.inner X m k D W hDW A hA : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val)) :=
    fun h => hxA ((NestedSupportPoints.preimage_mem_iff X.carrier A.val W.val hAW _ hxW).mp h)
  rw [RestrictedSupportRelation.term, NestedCycleRelation.Principal.coefficient _ _ _ _ _ C hxW, dite_eq_right hn]

theorem coefficient (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (a b : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW))
    (ha : a ∉ (Support.DivisorPrime.prime X k W (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW A.val
      (Divisor.SupportCycle.support_subset X m k D W hDW A hA).2 hxA).asIdeal)
    (hb : b ∉ (Support.DivisorPrime.prime X k W (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW A.val
      (Divisor.SupportCycle.support_subset X m k D W hDW A hA).2 hxA).asIdeal)
    (hab : g = algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW)) (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField a /
      algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW)) (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField b) :
    let p := Support.DivisorPrime.prime X k W (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW A.val
      (Divisor.SupportCycle.support_subset X m k D W hDW A hA).2 hxA
    RestrictedSupportRelation.term X m k D W hDW g hunit A hA C =
      CanonicalSurfaceReciprocity.restrictedOrder ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW)) p a -
      CanonicalSurfaceReciprocity.restrictedOrder ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW)) p b := by
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW
  let Z := RestrictedSupportRelation.inner X m k D W hDW A hA
  let hAW := (Divisor.SupportCycle.support_subset X m k D W hDW A hA).2
  have hyZ : y ∈ (Z : Set Y) :=
    (NestedSupportPoints.preimage_mem_iff X.carrier A.val W.val hAW _ hxW).mpr hxA
  let p := Support.DivisorPrime.prime X k W (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW A.val hAW hxA
  have hp : Stalk.PrimeQuotient.kernelPrime Y Z y hyZ = p :=
    Support.NestedPrimeComparison.prime_eq X k W A.val hAW _ hxW hxA
  let σ := Local.Principal.supportStalkMap Y Z y hyZ
  have hk : RingHom.ker σ.hom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hp
  have haσ : σ a ≠ 0 := fun h => ha (hk ▸ RingHom.mem_ker.mpr h)
  have hbσ : σ b ≠ 0 := fun h => hb (hk ▸ RingHom.mem_ker.mpr h)
  have hz : CycleClass.Thom.IntersectionGeometry.supportPoint Z ∈ (Z : Set Y) :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
  have hfun := Support.FractionIdentity.eq Y Z hz y hyZ (RestrictedSupportRelation.unit X m k D W hDW g hunit A hA)
    (RestrictedSupportRelation.unit_isUnit X m k D W hDW g hunit A hA) a b hbσ
      ((RestrictedSupportRelation.unit_function X m k D W hDW g hunit A hA).trans hab)
  change RestrictedSupportRelation.function X m k D W hDW g hunit A hA = _ at hfun
  have hy : Order.coheight y = 2 := by
    let A' : X.DimensionCycleSupport (k + 1) := ⟨A.val, by rw [A.property]; omega⟩
    let C' : X.DimensionCycleSupport (k + 2) := ⟨C.val, by rw [C.property]; omega⟩
    exact Relative.SupportSurfaceStalk.coheight_two X m k W A' C' hAW hxA hxW
  have ho := Support.StalkRatioOrder.order Y Z (RestrictedSupportRelation.inner_height X m k D W hDW A hA) y hy hyZ a b haσ hbσ
  rw [hp] at ho
  rw [RestrictedSupportRelation.term, NestedCycleRelation.Principal.coefficient _ _ _ _ _ C hxW, dite_eq_left hyZ, hfun]
  exact ho

end

/-! Support vanishing for the native restricted principal relation. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Vanishing

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedSupportRelation

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport k) (hDW : ¬ W.val ≤ D.val)
  (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField)
  (hunit : ∀ y : CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val, Order.coheight y = 1 →
    CycleClass.Geometric.GenericPoint.reducedSupportι W.val y ∈ (D.val : Set X.carrier) →
      ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y, IsUnit u ∧
        algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y)
          (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = g)

theorem term_zero (A : X.DimensionCycleSupport (1 + k))
    (hA : A ∈ (Divisor.SupportCycle.cycle X m k D W).support)
    (C : X.DimensionCycleSupport (1 + (k + 1))) (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∉ (A.val : Set X.carrier)) :
    RestrictedSupportRelation.term X m k D W hDW g hunit A hA C = 0 := by
  by_cases hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W.val : Set X.carrier)
  · exact zero_outside X m k D W hDW g hunit A hA C hxW hxA
  · exact NestedCycleRelation.Principal.coefficient_zero X (1 + (k + 1)) W.val _ _ C hxW

theorem cycle_zero (C : X.DimensionCycleSupport (1 + (k + 1)))
    (h : ∀ A ∈ (Divisor.SupportCycle.cycle X m k D W).support,
      CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∉ (A.val : Set X.carrier)) :
    RestrictedSupportRelation.cycle X m k D W hDW g hunit C = 0 := by
  simp only [RestrictedSupportRelation.cycle, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro A _
  rw [term_zero X m k D W hDW g hunit A.val A.property C (h A.val A.property), mul_zero]

end Vanishing

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedSupportCoefficient
