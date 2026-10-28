import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FactorOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AvoidingDivisorUnit
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ChowMoving

/-! # Principal Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrincipalCycle

noncomputable section

section

/-! A rational function whose divisor avoids an arbitrary support
restricts to a single nonzero rational function on it. Its native orders
are the actual divisor-intersection coefficients in every codimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace RestrictedOrder

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction.Restriction

theorem exists_restriction (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport q) (f : X.carrier.functionField) (hf : f ≠ 0)
    (hord : ∀ B : X.DimensionCycleSupport 1, A.val ≤ B.val →
      X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) = 0) :
    ∃ g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).functionField, g ≠ 0 ∧
      ∀ (C : X.DimensionCycleSupport (1 + q)) (hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier)),
        ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).ord g (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx) : ℚ) =
          (Principal.Integral.Cycle.cycle X f).sum
            (fun D c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A.val C.val) := by
  have hz : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ (A.val : Set X.carrier) :=
    (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem
  obtain ⟨u, hu, huf⟩ := AvoidingDivisorUnit.exists_unit X m A.val f hf hord
  let g := Support.LocalFraction.Restriction.toFunctionField X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) hz u
  have hg : g ≠ 0 := (hu.map (Support.LocalFraction.Restriction.toFunctionField X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) hz).hom).ne_zero
  refine ⟨g, hg, ?_⟩
  intro C hx
  let C' : X.DimensionCycleSupport (q + 1) := ⟨C.val, by rw [C.property]; omega⟩
  obtain ⟨a, b, ha, hb, habf, habg⟩ := Support.LocalFraction.exists_fraction X.carrier A.val hz
    (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx u hu
  rw [huf] at habf
  have he := FactorOrder.PrincipalLocal.ratio X m q A C' hx a b ha hb
  dsimp only at he
  change g =
    algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx))
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).functionField
        (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx a) /
    algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx))
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).functionField
        (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx b) at habg
  rw [← habf, ← habg] at he
  exact he.symm

end RestrictedOrder

end

/-! Intersecting a rational principal divisor with any support that avoids
its divisor supports gives the actual principal divisor
of the restricted function. Hence this intersection is rationally zero. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

theorem exists_principal_intersection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport q) (f : X.carrier.functionField) (hf : f ≠ 0)
    (hord : ∀ B : X.DimensionCycleSupport 1, A.val ≤ B.val →
      X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) = 0)
    (d : X.RationalDimensionCycle 1)
    (hd : ∀ B : X.DimensionCycleSupport 1, d B = (X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) : ℚ)) :
    ∃ g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).functionField, g ≠ 0 ∧
      CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 q d (Finsupp.single A 1) (Principal.ClosedSectionCycle.principalCycle X (1 + q) A.val g) := by
  obtain ⟨g, hg, hlocal⟩ := RestrictedOrder.exists_restriction X m q A f hf hord
  refine ⟨g, hg, ?_, ?_⟩
  · intro B hB D hD C hC
    have hDA : D = A := by simpa using hD
    subst D
    have hCA : C ≤ A.val := fun _ hx => (hC hx).2
    have hn : C ≠ A.val := by
      intro he
      have hAB : A.val ≤ B.val := fun x hx => (hC (he ▸ hx)).1
      apply Finsupp.mem_support_iff.mp hB
      rw [hd, hord B hAB, Int.cast_zero]
    have hh := Supports.codimension_strictAnti X m (lt_of_le_of_ne hCA hn)
    rw [A.property] at hh
    omega
  · intro C
    rw [Principal.ClosedSectionCycle.principalCycle_apply]
    simp only [Finsupp.sum_single_index, mul_zero, zero_mul, mul_one]
    by_cases hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier)
    · rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hx]
      have heq : d = Principal.Integral.Cycle.cycle X f := Finsupp.ext (fun B =>
        (hd B).trans (Principal.Integral.Cycle.cycle_apply X f B).symm)
      rw [heq]
      exact hlocal C hx
    · rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hx]
      symm
      apply Finset.sum_eq_zero
      intro B _
      have hz : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val = 0 :=
        dite_eq_right (fun h => hx h.2)
      change d B * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val = 0
      rw [hz, mul_zero]

theorem intersection_rationally_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport q) (f : X.carrier.functionField) (hf : f ≠ 0)
    (hord : ∀ B : X.DimensionCycleSupport 1, A.val ≤ B.val →
      X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) = 0)
    (d : X.RationalDimensionCycle 1)
    (hd : ∀ B : X.DimensionCycleSupport 1, d B = (X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) : ℚ))
    (c : X.RationalDimensionCycle (1 + q))
    (hc : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 q d (Finsupp.single A 1) c) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (1 + q) c 0 := by
  obtain ⟨g, hg, hi⟩ := exists_principal_intersection X m q A f hf hord d hd
  have he := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 1 q hc hi
  change c - 0 ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + q)
  rw [sub_zero, he]
  exact Submodule.subset_span (Principal.ClosedSectionCycle.principalCycle_isPrincipalDivisor X (1 + q) A.val
    (by rw [A.property]; omega) g hg)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrincipalCycle
