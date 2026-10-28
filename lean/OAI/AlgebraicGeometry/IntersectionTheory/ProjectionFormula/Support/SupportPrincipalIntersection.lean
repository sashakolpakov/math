import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedSupportSum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.PrincipalLocalCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Principal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedSupportCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SupportFractions
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfaceRatioReciprocity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalEquations

/-! # Support Principal Intersection -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.SupportPrincipalIntersection

noncomputable section

/-! Intersection of a divisor with a principal cycle on an arbitrary
support is an actual principal-divisor relation when the support function
is a unit along the divisor-intersection components. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
  (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport k) (hDW : ¬ W.val ≤ D.val)
  (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
  (hunit : ∀ y : CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val, Order.coheight y = 1 →
    CycleClass.Geometric.GenericPoint.reducedSupportι W.val y ∈ (D.val : Set X.carrier) →
      ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y, IsUnit u ∧
        algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y)
          (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = g)

include hg

theorem coefficient (C : X.DimensionCycleSupport (1 + (k + 1))) :
    (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g).sum (fun A c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A.val C.val) =
      RestrictedSupportRelation.cycle X m k D W hDW g hunit C := by
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  by_cases hxW : x ∈ (W.val : Set X.carrier)
  · by_cases hxD : x ∈ (D.val : Set X.carrier)
    · have hCW : C.val ≤ W.val := (Supports.supportPoint_mem_iff_subset
        (⟨(W.val : Set X.carrier), W.val.isClosed⟩ : Closeds X.carrier) C.val).mp hxW
      obtain ⟨A, hCA, hAW⟩ := IntermediateSupports.next_support X m k (1 + (k + 1)) W C (by omega) hCW
      have hxA : x ∈ (A.val : Set X.carrier) :=
        hCA (C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed).mem
      let C' : X.DimensionCycleSupport (k + 2) := ⟨C.val, by rw [C.property]; omega⟩
      obtain ⟨r, hr, he⟩ := Smooth.LocalEquations.exists_equation X m D x hxD
      obtain ⟨a, b, ha, hb, havoid, hab⟩ :=
        Local.SupportFractions.exists_fraction X m k D W hDW x hxD hxW r hr he g hg hunit
      let R := (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)
      let f := Local.Principal.supportStalkMap X.carrier W.val x hxW r
      have hf : f ≠ 0 := Local.SupportMultiplicity.restricted_nonzero X k D W hDW x hxD hxW r he
      have hdim : (IsLocalRing.maximalIdeal R).height = 2 :=
        Relative.SupportSurfaceStalk.maximal_height X m k W A C' hAW hxA hxW
      have hrec := SurfaceRatioReciprocity.order_sums_eq R hdim f a b hf ha hb
        (fun p _ hp hfp => (havoid ⟨p, inferInstance⟩ hp hfp).1)
        (fun p _ hp hfp => (havoid ⟨p, inferInstance⟩ hp hfp).2)
      have hleft := PrincipalLocalCoefficient.Sum.coefficient X m k D W C' hxD hxW r hr he g a b ha hb havoid hab
      have hright := RestrictedSupportSum.coefficient X m k D W hDW g hunit C hxD hxW r hr he a b havoid hab
      exact hleft.trans (hrec.symm.trans hright.symm)
    · have hl : (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g).sum
          (fun A c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A.val C.val) = 0 := by
        apply Finset.sum_eq_zero
        intro B _
        have hz : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val B.val C.val = 0 := dite_eq_right (fun h => hxD h.1)
        exact (congrArg (fun t : ℚ => Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g B * t) hz).trans (mul_zero _)
      have hr := RestrictedSupportCoefficient.Vanishing.cycle_zero X m k D W hDW g hunit C (by
        intro B hB hxB
        exact hxD ((Divisor.SupportCycle.support_subset X m k D W hDW B hB).1 hxB))
      exact hl.trans hr.symm
  · have hl : (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g).sum
        (fun A c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A.val C.val) = 0 := by
      apply Finset.sum_eq_zero
      intro A hA
      have hxA : x ∉ (A.val : Set X.carrier) := fun h =>
        hxW (Principal.subset X k W g A hA h)
      have hz : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A.val C.val = 0 := dite_eq_right (fun h => hxA h.2)
      exact (congrArg (fun t : ℚ => Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g A * t) hz).trans (mul_zero _)
    have hr := RestrictedSupportCoefficient.Vanishing.cycle_zero X m k D W hDW g hunit C (by
      intro A hA hxA
      exact hxW ((Divisor.SupportCycle.support_subset X m k D W hDW A hA).2 hxA))
    exact hl.trans hr.symm

theorem isProper : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 (k + 1) (Finsupp.single D 1)
    (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) (RestrictedSupportRelation.cycle X m k D W hDW g hunit) := by
  refine ⟨Principal.proper X m k D W g hunit, ?_⟩
  intro C
  rw [Finsupp.sum_single_index]
  · simpa only [one_mul] using (coefficient X m k D W hDW g hg hunit C).symm
  · simp

theorem intersection_eq :
    Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) (Finsupp.single D 1)
      (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) = RestrictedSupportRelation.cycle X m k D W hDW g hunit :=
  CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 1 (k + 1)
    (Supports.ProperCycle.intersectionBilinear_isProper X m 1 (k + 1) _ _
      (Principal.proper X m k D W g hunit))
    (isProper X m k D W hDW g hg hunit)

include hDW hunit in
theorem intersection_rationally_zero :
    Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) (Finsupp.single D 1)
      (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + (k + 1)) := by
  rw [intersection_eq X m k D W hDW g hg hunit]
  exact RestrictedSupportRelation.cycle_mem X m k D W hDW g hunit

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.SupportPrincipalIntersection
