import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FactorOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UnitDivisorSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.CycleMoving

/-! # Specified Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpecifiedCycle

noncomputable section

/-! The principal intersection formula with a specified generic unit.
The restricted function is the actual image of that unit in the support
function field, so later norm comparisons retain its identity. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction.Restriction OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem isProperIntersection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport q) (hz : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ (A.val : Set X.carrier))
    (u : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)) (hu : IsUnit u)
    (d : X.RationalDimensionCycle 1)
    (hd : ∀ B : X.DimensionCycleSupport 1, d B =
      (X.carrier.ord (algebraMap (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)) X.carrier.functionField u)
        (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) : ℚ)) :
    CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 q d (Finsupp.single A 1)
      (Principal.ClosedSectionCycle.principalCycle X (1 + q) A.val (Support.LocalFraction.Restriction.toFunctionField X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) hz u)) := by
  let f := algebraMap (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)) X.carrier.functionField u
  let g := Support.LocalFraction.Restriction.toFunctionField X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) hz u
  constructor
  · apply Divisor.CycleMoving.of_avoiding X m q
    intro B hB E hE hEB
    have hEA : E = A := by simpa using hE
    subst E
    have hs : CycleClass.Thom.IntersectionGeometry.supportPoint B.val ⤳ CycleClass.Thom.IntersectionGeometry.supportPoint A.val :=
      (B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).specializes (hEB hz)
    have ho := UnitDivisorSupport.order_zero X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) hs u hu
    apply Finsupp.mem_support_iff.mp hB
    rw [hd, ho, Int.cast_zero]
  · intro C
    rw [Principal.ClosedSectionCycle.principalCycle_apply]
    simp only [Finsupp.sum_single_index, mul_zero, zero_mul, mul_one]
    by_cases hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier)
    · rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hx]
      obtain ⟨a, b, ha, hb, habf, habg⟩ := Support.LocalFraction.exists_fraction X.carrier A.val hz
        (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx u hu
      let C' : X.DimensionCycleSupport (q + 1) := ⟨C.val, by rw [C.property]; omega⟩
      have he := FactorOrder.PrincipalLocal.ratio X m q A C' hx a b ha hb
      dsimp only at he
      rw [← habf] at he
      change g =
        algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx))
          (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).functionField
            (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx a) /
        algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx))
          (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).functionField
            (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx b) at habg
      rw [← habg] at he
      have heq : d = Principal.Integral.Cycle.cycle X f := Finsupp.ext (fun B =>
        (hd B).trans (Principal.Integral.Cycle.cycle_apply X f B).symm)
      rw [heq]
      exact he.symm
    · rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hx]
      symm
      apply Finset.sum_eq_zero
      intro B _
      have he : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val = 0 := dite_eq_right (fun h => hx h.2)
      change d B * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val = 0
      rw [he, mul_zero]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpecifiedCycle
