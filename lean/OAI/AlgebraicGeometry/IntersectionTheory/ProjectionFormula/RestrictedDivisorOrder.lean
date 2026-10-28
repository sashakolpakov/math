import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.GenericUnit
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicDivisorRatio

/-! # Restricted Divisor Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedDivisorOrder

noncomputable section

/-! A rational function with zero order on a divisor restricts to one
nonzero rational function on that divisor. At every codimension-two point,
its order is the sum of the ambient divisor orders times the exact
geometric Tor intersection multiplicities. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction.Restriction OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem exists_restriction (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport 1) (f : X.carrier.functionField) (hf : f ≠ 0)
    (hord : X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = 0) :
    ∃ g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).functionField, g ≠ 0 ∧
      ∀ (C : X.DimensionCycleSupport 2) (hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier)),
        ∃ S : Finset (Spec (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))),
          (∀ p ∈ S, p.asIdeal.height = 1 ∧
            X.supportCodimension (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) = 1) ∧
          (∀ p : Spec (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)),
            p.asIdeal.height = 1 → p ∉ S →
              X.carrier.ord f (X.carrier.fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) = 0) ∧
          ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).ord g (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx) : ℚ) =
            ∑ p ∈ S, (X.carrier.ord f (X.carrier.fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) : ℚ) *
              CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) A.val C.val := by
  have hz : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ (A.val : Set X.carrier) :=
    (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem
  obtain ⟨u, hu, huf⟩ := Divisor.GenericUnit.exists_unit_of_order_zero X m A f hf hord
  let g := Support.LocalFraction.Restriction.toFunctionField X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) hz u
  have hg : g ≠ 0 := (hu.map (Support.LocalFraction.Restriction.toFunctionField X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) hz).hom).ne_zero
  refine ⟨g, hg, ?_⟩
  intro C hx
  obtain ⟨a, b, ha, hb, habf, habg⟩ := Support.LocalFraction.exists_fraction X.carrier A.val hz
    (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx u hu
  rw [huf] at habf
  obtain ⟨S, hS, hout, he⟩ := IntrinsicDivisorRatio.Intrinsic.order_ratio_eq_sum X m A C hx a b ha hb
  rw [← habf] at hout he
  change g =
    algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx))
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).functionField
        (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx a) /
    algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx))
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).functionField
        (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx b) at habg
  rw [← habg] at he
  exact ⟨S, hS, hout, he⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedDivisorOrder
