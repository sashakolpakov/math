import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportStalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalOrder

/-! # Principal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Principal

noncomputable section

/-! Principal cycles are supported on their defining support. A function
that is a unit along its divisor intersection meets that divisor properly. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

theorem subset (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ) (W : X.DimensionCycleSupport k)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField)
    (A : X.DimensionCycleSupport (k + 1)) (hA : A ∈ (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g).support) : A.val ≤ W.val := by
  have hp : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ (W.val : Set X.carrier) := by
    by_contra h
    exact Finsupp.mem_support_iff.mp hA (by
      rw [Principal.ClosedSectionCycle.principalCycle_apply, CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right h])
  exact (Supports.supportPoint_mem_iff_subset
    (⟨(W.val : Set X.carrier), W.val.isClosed⟩ : Closeds X.carrier) A.val).mp hp

theorem avoids (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField)
    (hunit : ∀ y : CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val, Order.coheight y = 1 →
      CycleClass.Geometric.GenericPoint.reducedSupportι W.val y ∈ (D.val : Set X.carrier) →
        ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y, IsUnit u ∧
          algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y)
            (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = g)
    (A : X.DimensionCycleSupport (k + 1)) (hA : A ∈ (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g).support) : ¬ A.val ≤ D.val := by
  intro hAD
  have hxW : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ (W.val : Set X.carrier) :=
    subset X k W g A hA (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) hxW
  have hy : Order.coheight y = 1 := AdjacentSupportStalk.coheight_one X m k W A hxW
  have hyD : CycleClass.Geometric.GenericPoint.reducedSupportι W.val y ∈ (D.val : Set X.carrier) := by
    rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
    exact hAD (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem
  obtain ⟨u, hu, hug⟩ := hunit y hy hyD
  apply Finsupp.mem_support_iff.mp hA
  rw [Principal.ClosedSectionCycle.principalCycle_apply, CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hxW, ← hug,
    Affine.PrincipalOrder.stalk_order _ y hy u hu.ne_zero, Ring.ord_of_isUnit hu]
  rfl

theorem proper (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField)
    (hunit : ∀ y : CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val, Order.coheight y = 1 →
      CycleClass.Geometric.GenericPoint.reducedSupportι W.val y ∈ (D.val : Set X.carrier) →
        ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y, IsUnit u ∧
          algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y)
            (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = g) :
    CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) (Finsupp.single D 1) (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) := by
  intro B hB A hA C hC
  have hBD : B = D := by simpa using hB
  subst B
  have hCA : C ≤ A.val := fun _ hx => (hC hx).2
  have hn : C ≠ A.val := by
    intro he
    exact avoids X m k D W g hunit A hA (fun x hx => (hC (he ▸ hx)).1)
  have hh := Supports.codimension_strictAnti X m (lt_of_le_of_ne hCA hn)
  rw [A.property] at hh
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Principal
