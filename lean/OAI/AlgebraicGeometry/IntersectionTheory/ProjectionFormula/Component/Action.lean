import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntersectionZero
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

/-! # Action -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Action

noncomputable section

/-! Selection by an open component preserves the actual principal-divisor
relations. Its bilinear extension is the cycle action of codimension-zero
classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical BigOperators

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

def selectCycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (q : ℕ)
    (A : X.DimensionCycleSupport 0) :
    X.RationalDimensionCycle q →ₗ[ℚ] X.RationalDimensionCycle q where
  toFun b := b.filter (fun B => B.val ≤ A.val)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

theorem selectCycle_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (q : ℕ)
    (A : X.DimensionCycleSupport 0) (b : X.RationalDimensionCycle q)
    (C : X.DimensionCycleSupport q) :
    selectCycle X q A b C = if C.val ≤ A.val then b C else 0 := rfl

theorem select_principal (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A : X.DimensionCycleSupport 0)
    (W : IrreducibleCloseds X.carrier) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    selectCycle X q A (Principal.ClosedSectionCycle.principalCycle X q W g) =
      if W ≤ A.val then Principal.ClosedSectionCycle.principalCycle X q W g else 0 := by
  ext C
  rw [selectCycle_apply]
  by_cases hW : W ≤ A.val
  · rw [ite_eq_left hW]
    by_cases hC : C.val ≤ A.val
    · rw [ite_eq_left hC]
    · rw [ite_eq_right hC, Principal.ClosedSectionCycle.principalCycle_apply, CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right]
      intro hx
      exact hC ((Supports.supportPoint_mem_iff_subset
        ⟨W, W.isClosed⟩ C.val).mp hx |>.trans hW)
  · rw [ite_eq_right hW, Finsupp.zero_apply]
    by_cases hC : C.val ≤ A.val
    · rw [ite_eq_left hC, Principal.ClosedSectionCycle.principalCycle_apply, CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right]
      intro hx
      have hc : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (C.val : Set X.carrier) :=
        (C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed).mem
      exact hW (IntersectionZero.subset_of_mem_zero_support X m A W
        (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx (hC hc))
    · rw [ite_eq_right hC]

theorem select_preserves_relations (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A : X.DimensionCycleSupport 0) :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences X q ≤ (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X q).comap (selectCycle X q A) := by
  apply Submodule.span_le.mpr
  intro d hd
  obtain ⟨W, hW, g, hg, rfl⟩ := (Principal.ClosedSectionCycle.isPrincipalDivisor_iff X q d).mp hd
  change selectCycle X q A (Principal.ClosedSectionCycle.principalCycle X q W g) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X q
  rw [select_principal X m]
  split
  · exact Submodule.subset_span (Principal.ClosedSectionCycle.principalCycle_isPrincipalDivisor X q W hW g hg)
  · exact Submodule.zero_mem _

def cycleAction (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (q : ℕ) :
    X.RationalDimensionCycle 0 →ₗ[ℚ] X.RationalDimensionCycle q →ₗ[ℚ]
      X.RationalDimensionCycle q :=
  Finsupp.linearCombination ℚ (selectCycle X q)

theorem cycleAction_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (q : ℕ)
    (a : X.RationalDimensionCycle 0) (b : X.RationalDimensionCycle q)
    (C : X.DimensionCycleSupport q) :
    cycleAction X q a b C =
      a.sum (fun A r => r * if C.val ≤ A.val then b C else 0) := by
  simp only [cycleAction, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, selectCycle_apply]

theorem cycleAction_preserves_relations (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (a : X.RationalDimensionCycle 0) :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences X q ≤ (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X q).comap (cycleAction X q a) := by
  intro b hb
  change cycleAction X q a b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X q
  simp only [cycleAction, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun A _ => Submodule.smul_mem _ _
    (select_preserves_relations X m q A hb)

theorem rationalEquivalences_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 0 = ⊥ := by
  apply le_antisymm (Submodule.span_le.mpr ?_) bot_le
  rintro d ⟨W, hW, _⟩
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Action
