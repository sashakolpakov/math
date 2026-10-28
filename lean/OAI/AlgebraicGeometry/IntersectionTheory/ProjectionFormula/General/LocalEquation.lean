import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeEquationOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpecifiedCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.FractionIdentity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Integral
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AvoidingDivisorUnit

/-! # Local Equation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.LocalEquation

noncomputable section

/-! A local equation for a divisor computes the divisor intersection
coefficients along every support through that local point, in any codimension.
The proof compares with the already constructed native principal cycle. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction.Restriction OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

theorem principal_sum (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport q) (x : X.carrier)
    (hxD : x ∈ (D.val : Set X.carrier))
    (r : X.carrier.presheaf.stalk x) (hr : r ≠ 0)
    (he : RingHom.ker (Local.Principal.supportStalkMap X.carrier D.val x hxD).hom = Ideal.span {r})
    (A : X.DimensionCycleSupport (1 + q)) (hxA : x ∈ (A.val : Set X.carrier)) :
    (Principal.Integral.Cycle.cycle X (algebraMap (X.carrier.presheaf.stalk x) X.carrier.functionField r)).sum
      (fun B c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val W.val A.val) =
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val W.val A.val := by
  let F := algebraMap (X.carrier.presheaf.stalk x) X.carrier.functionField r
  let d := Principal.Integral.Cycle.cycle X F
  have hD : d D = 1 := by
    rw [Principal.Integral.Cycle.cycle_apply, PrimeEquationOrder.geometric X m D D x hxD hxD r hr he,
      ite_eq_left rfl, Int.cast_one]
  change ∑ B ∈ d.support, d B * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val W.val A.val = _
  rw [Finset.sum_eq_single D]
  · rw [hD, one_mul]
  · intro B _ hBD
    by_cases hi : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val W.val A.val = 0
    · rw [hi, mul_zero]
    · have hzB : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ (B.val : Set X.carrier) := by
        by_contra hn
        exact hi (dite_eq_right (fun h => hn h.1))
      have hAB : A.val ≤ B.val :=
        (Supports.supportPoint_mem_iff_subset
          (⟨(B.val : Set X.carrier), B.val.isClosed⟩ : Closeds X.carrier) A.val).mp hzB
      have hdB : d B = 0 := by
        rw [Principal.Integral.Cycle.cycle_apply,
          PrimeEquationOrder.geometric X m D B x hxD (hAB hxA) r hr he,
          ite_eq_right hBD, Int.cast_zero]
      rw [hdB, zero_mul]
  · intro hn
    exact (hn (Finsupp.mem_support_iff.mpr (hD ▸ one_ne_zero))).elim

theorem order_eq (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport q) (hWD : ¬ W.val ≤ D.val) (x : X.carrier)
    (hxD : x ∈ (D.val : Set X.carrier)) (hxW : x ∈ (W.val : Set X.carrier))
    (r : X.carrier.presheaf.stalk x) (hr : r ≠ 0)
    (he : RingHom.ker (Local.Principal.supportStalkMap X.carrier D.val x hxD).hom = Ideal.span {r})
    (A : X.DimensionCycleSupport (1 + q)) (hxA : x ∈ (A.val : Set X.carrier))
    (hAW : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ (W.val : Set X.carrier)) :
    ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).ord
      (algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW))
        (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField (Local.Principal.supportStalkMap X.carrier W.val x hxW r))
      (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) hAW) : ℚ) =
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val W.val A.val := by
  let F := algebraMap (X.carrier.presheaf.stalk x) X.carrier.functionField r
  let d := Principal.Integral.Cycle.cycle X F
  have hF : F ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hr
  have hFW (B : X.DimensionCycleSupport 1) (hWB : W.val ≤ B.val) :
      X.carrier.ord F (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) = 0 := by
    rw [PrimeEquationOrder.geometric X m D B x hxD (hWB hxW) r hr he, ite_eq_right]
    intro hBD
    subst B
    exact hWD hWB
  obtain ⟨u, hu, huF⟩ := AvoidingDivisorUnit.exists_unit X m W.val F hF hFW
  have hzW : CycleClass.Thom.IntersectionGeometry.supportPoint W.val ∈ (W.val : Set X.carrier) :=
    (W.val.isIrreducible.isGenericPoint_genericPoint W.val.isClosed).mem
  have hgu := Support.FractionIdentity.eq X.carrier W.val hzW x hxW u hu r 1
    (by rw [map_one]; exact one_ne_zero) (by simpa only [map_one, div_one] using huF)
  rw [map_one, div_one] at hgu
  have hc := SpecifiedCycle.isProperIntersection X m q W hzW u hu d
    (fun B => by rw [huF]; exact Principal.Integral.Cycle.cycle_apply X F B)
  have hcoef := hc.2 A
  rw [Principal.ClosedSectionCycle.principalCycle_apply, CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hAW, hgu] at hcoef
  simp only [Finsupp.sum_single_index, mul_zero, zero_mul, mul_one] at hcoef
  exact hcoef.trans (principal_sum X m q D W x hxD r hr he A hxA)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.LocalEquation
