import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Action

/-! # Zero Components -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ZeroComponents

noncomputable section

/-! Codimension-zero supports are exactly the open integral components.
The reduced fundamental cycle has coefficient one on each of them. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

def componentSupport (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier) :
    IrreducibleCloseds X.carrier :=
  ⟨C.val, C.property.1, isClosed_of_mem_irreducibleComponents _ C.property⟩

theorem component_codimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (C : irreducibleComponents X.carrier) :
    X.supportCodimension (componentSupport X C) = 0 := by
  let D := componentSupport X C
  have hD : IsOpen (D : Set X.carrier) :=
    Foundations.Scheme.LocalDomainComponents.isOpen_irreducibleComponent_of_stalkDomains X.stalk_isDomain
      (NoetherianSpace.finite_irreducibleComponents (α := X.carrier)) C.property
  let : IsOpenImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι D) := Open.Support.inclusion_isOpenImmersion D hD
  let : SmoothOfRelativeDimension m (CycleClass.Geometric.SupportFiniteType.supportStructureMap D X.structureMap) := by
    have h := smoothOfRelativeDimension_comp 0 m (CycleClass.Geometric.GenericPoint.reducedSupportι D) X.structureMap
    simpa only [zero_add, CycleClass.Geometric.SupportFiniteType.supportStructureMap] using h
  have hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D X.structureMap = m :=
    Grading.integral_dimension_of_relativeDimension (CycleClass.Geometric.SupportFiniteType.supportStructureMap D X.structureMap) m
  have h := Grading.supportDimension_add_codimension X m D
  rw [hd] at h
  change X.supportCodimension D = 0
  omega

def containingComponent (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (W : IrreducibleCloseds X.carrier) :
    X.DimensionCycleSupport 0 :=
  ⟨componentSupport X (X.supportComponent W), component_codimension X m _⟩

theorem subset_containingComponent (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (W : IrreducibleCloseds X.carrier) :
    W ≤ (containingComponent X m W).val := X.support_subset_component W

theorem containingComponent_unique (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (W : IrreducibleCloseds X.carrier)
    (A : X.DimensionCycleSupport 0) (hA : W ≤ A.val) : containingComponent X m W = A := by
  obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
  have hC : (containingComponent X m W).val ≤ A.val :=
    IntersectionZero.subset_of_mem_zero_support X m A (containingComponent X m W).val x
      (subset_containingComponent X m W hx) (hA hx)
  exact Subtype.ext (IntersectionZero.eq_of_subset_of_codimension_eq X m hC
    ((containingComponent X m W).property.trans A.property.symm))

theorem subset_zero_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (W : IrreducibleCloseds X.carrier)
    (A : X.DimensionCycleSupport 0) : W ≤ A.val ↔ A = containingComponent X m W := by
  constructor
  · intro h
    exact (containingComponent_unique X m W A h).symm
  · rintro rfl
    exact subset_containingComponent X m W

theorem reducedClosedCycle_zero_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (S : Closeds X.carrier)
    (A : X.DimensionCycleSupport 0) :
    CycleClass.Thom.IntersectionGeometry.reducedClosedCycle X 0 S A = if (A.val : Set X.carrier) ⊆ S then 1 else 0 := by
  rw [CycleClass.Thom.IntersectionGeometry.reducedClosedCycle_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨C, hC⟩
    rw [← hC]
    exact Supports.closedComponentSupport_subset X.carrier S C
  · intro hA
    exact Supports.support_eq_component X m 0 S (fun _ _ => Nat.zero_le _) A hA

theorem fundamentalCycle_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A : X.DimensionCycleSupport 0) :
    ProperCycleLinearity.fundamentalCycle X A = 1 := by
  rw [ProperCycleLinearity.fundamentalCycle, reducedClosedCycle_zero_apply X m]
  exact ite_eq_left (Set.subset_univ _)

theorem cycleAction_apply_component (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle 0) (b : X.RationalDimensionCycle q)
    (C : X.DimensionCycleSupport q) :
    Component.Action.cycleAction X q a b C = a (containingComponent X m C.val) * b C := by
  rw [Component.Action.cycleAction_apply]
  have hc (A : X.DimensionCycleSupport 0) : C.val ≤ A.val ↔ A = containingComponent X m C.val := by
    constructor
    · intro h
      exact (containingComponent_unique X m C.val A h).symm
    · rintro rfl
      exact subset_containingComponent X m C.val
  simp only [Finsupp.sum, hc, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases h : containingComponent X m C.val ∈ a.support
  · simp [h]
  · have hz := Finsupp.notMem_support_iff.mp h
    simp [h, hz]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ZeroComponents
