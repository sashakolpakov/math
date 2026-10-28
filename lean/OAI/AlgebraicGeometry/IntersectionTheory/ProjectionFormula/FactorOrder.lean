import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.FactorCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SumCongruence

/-! # Factor Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FactorOrder

noncomputable section

section

/-! The local factor cycle of a function intersects any properly met
support with coefficient equal to the restricted function's actual order. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal UniqueFactorizationMonoid

theorem order (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport q) (C : X.DimensionCycleSupport (q + 1))
    [UniqueFactorizationMonoid (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))]
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (a : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
    (ha : Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA a ≠ 0) :
    (Local.FactorCycle.cycle X m (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) a).sum
      (fun D c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A.val C.val) =
      ((Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA))
          (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA a)).toNat : ℚ) := by
  let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
  let : IsDomain R := X.stalk_isDomain (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
  let S := (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA)
  let σ := Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA
  let : Ring.KrullDimLE 1 S := krullDimLE_of_coheight_le
    (AdjacentSupportStalk.coheight_one X m q A C hxA).le
  have ha0 : a ≠ 0 := fun hz => ha (by rw [hz, map_zero])
  have hfactor (r : R) (hr : r ∈ factors a) : σ r ≠ 0 := by
    obtain ⟨b, hb⟩ := dvd_of_mem_factors hr
    intro hz
    apply ha
    change σ a = 0
    rw [hb, map_mul, hz, zero_mul]
  rw [Local.FactorCycle.weighted_sum, FactorOrderSum.rational_factors R S σ.hom a ha0 ha]
  have hsum := Multiset.attach_map_val' (factors a)
    (fun r => ((Ring.ord S (σ r)).toNat : ℚ))
  rw [← hsum]
  congr 1
  apply Multiset.map_congr rfl
  intro r _
  exact Local.PrimeFactorSupport.multiplicity X m q A C hxA r.val
    (prime_of_factor r.val r.property) (hfactor r.val r.property)

end

/-! The native principal divisor of a local function, or a quotient of
local functions, intersects an arbitrary support by the native order of
its restriction. No bound on the ambient dimension or codimension is used. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace PrincipalLocal

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem order (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport q) (C : X.DimensionCycleSupport (q + 1))
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (a : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
    (ha : Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA a ≠ 0) :
    (Principal.Integral.Cycle.cycle X
      (algebraMap (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) X.carrier.functionField a)).sum
      (fun D c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A.val C.val) =
      ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).ord
        (algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk
          (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA)) (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).functionField
          (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA a))
        (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA) : ℚ) := by
  let : UniqueFactorizationMonoid (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) :=
    Smooth.LocalEquations.stalk_factorial X m (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
  have ha0 : a ≠ 0 := fun hz => ha (by rw [hz, map_zero])
  have he := Local.SumCongruence.sum_eq X 1 A.val C.val
    (Principal.Integral.Cycle.cycle X
      (algebraMap (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) X.carrier.functionField a))
    (Local.FactorCycle.cycle X m (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) a)
    (fun D hxD => (Principal.Integral.Cycle.cycle_apply X _ D).trans
      (Local.FactorCycle.coefficient X m (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) a ha0 D hxD).symm)
  rw [he, FactorOrder.order X m q A C hxA a ha,
    Affine.PrincipalOrder.stalk_order _ _ (AdjacentSupportStalk.coheight_one X m q A C hxA) _ ha,
    Int.cast_natCast]

theorem ratio (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport q) (C : X.DimensionCycleSupport (q + 1))
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (a b : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
    (ha : Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA a ≠ 0)
    (hb : Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA b ≠ 0) :
    let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val
    let y := CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA
    let σ := Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA
    (Principal.Integral.Cycle.cycle X
      (algebraMap R X.carrier.functionField a / algebraMap R X.carrier.functionField b)).sum
      (fun D c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A.val C.val) =
      (Y.ord (algebraMap (Y.presheaf.stalk y) Y.functionField (σ a) /
        algebraMap (Y.presheaf.stalk y) Y.functionField (σ b)) y : ℚ) := by
  intro R Y y σ
  let fa := algebraMap R X.carrier.functionField a
  let fb := algebraMap R X.carrier.functionField b
  let ga := algebraMap (Y.presheaf.stalk y) Y.functionField (σ a)
  let gb := algebraMap (Y.presheaf.stalk y) Y.functionField (σ b)
  have ha0 : a ≠ 0 := fun hz => ha (by rw [hz, map_zero])
  have hb0 : b ≠ 0 := fun hz => hb (by rw [hz, map_zero])
  have hfa : fa ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R X.carrier.functionField)).mpr ha0
  have hfb : fb ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R X.carrier.functionField)).mpr hb0
  have hga : ga ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ Y.functionField)).mpr ha
  have hgb : gb ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ Y.functionField)).mpr hb
  have hd : Principal.Integral.Cycle.cycle X (fa / fb) =
      Principal.Integral.Cycle.cycle X fa - Principal.Integral.Cycle.cycle X fb := by
    ext D
    rw [Finsupp.sub_apply, Principal.Integral.Cycle.cycle_apply, Principal.Integral.Cycle.cycle_apply,
      Principal.Integral.Cycle.cycle_apply, IntrinsicDivisorRatio.Intrinsic.ord_div X.carrier fa fb hfa hfb, Int.cast_sub]
  let F := Finsupp.linearCombination ℚ (fun D : X.DimensionCycleSupport 1 =>
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A.val C.val)
  change F (Principal.Integral.Cycle.cycle X (fa / fb)) = (Y.ord (ga / gb) y : ℚ)
  rw [hd, map_sub, IntrinsicDivisorRatio.Intrinsic.ord_div Y ga gb hga hgb, Int.cast_sub]
  exact congrArg₂ (fun u v : ℚ => u - v) (order X m q A C hxA a ha) (order X m q A C hxA b hb)

end PrincipalLocal

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FactorOrder
