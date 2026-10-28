import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedGenericRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Restricted Principal Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.RestrictedPrincipalCycle

noncomputable section

/-! The restricted rational function on each component of a finite
intersection cycle gives a native principal-divisor relation in the
next codimension. All weights are the original cycle coefficients. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem pair_support (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport p) (W : X.DimensionCycleSupport k)
    (hproper : Supports.ProperCycle.pairMeetsProperly X p k A W)
    (C : X.DimensionCycleSupport (p + k)) (hC : C ∈ (Supports.ProperCycle.pairCycle X m p k A W).support) :
    C.val ≤ A.val ∧ C.val ≤ W.val := by
  have hne := Finsupp.mem_support_iff.mp hC
  rw [Supports.ProperCycle.pairCycle_apply X m p k A W hproper] at hne
  have hpoint : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier) ∧
      CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W.val : Set X.carrier) := by
    by_contra h
    exact hne (dite_eq_right h)
  exact ⟨(Supports.supportPoint_mem_iff_subset ⟨_, A.val.isClosed⟩ C.val).mp hpoint.1,
    (Supports.supportPoint_mem_iff_subset ⟨_, W.val.isClosed⟩ C.val).mp hpoint.2⟩

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (q : ℕ) (W : IrreducibleCloseds X.carrier)
  (c : X.RationalDimensionCycle q) (hc : ∀ C ∈ c.support, C.val ≤ W)
  (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
  (hunit : ∀ C : c.support,
    ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk
      (NestedGenericRestriction.point X.carrier C.val.val W (hc C.val C.property)),
      IsUnit u ∧ algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField u = g)

def cycle : X.RationalDimensionCycle (q + 1) :=
  ∑ C : c.support, c C.val • Principal.ClosedSectionCycle.principalCycle X (q + 1) C.val.val
    (NestedGenericRestriction.function X.carrier C.val.val W (hc C.val C.property) g (hunit C))

theorem rationally_zero : cycle X q W c hc g hunit ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (q + 1) := by
  apply Submodule.sum_mem
  intro C _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact Principal.ClosedSectionCycle.principalCycle_isPrincipalDivisor X (q + 1) C.val.val (by rw [C.val.property])
    (NestedGenericRestriction.function X.carrier C.val.val W (hc C.val C.property) g (hunit C))
    (NestedGenericRestriction.function_ne_zero X.carrier C.val.val W (hc C.val C.property) g (hunit C))

theorem coefficient (D : X.DimensionCycleSupport (q + 1)) :
    cycle X q W c hc g hunit D =
      ∑ C : c.support, c C.val * CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient X C.val.val
        (NestedGenericRestriction.function X.carrier C.val.val W (hc C.val C.property) g (hunit C)) D.val := by
  simp only [cycle, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Principal.ClosedSectionCycle.principalCycle_apply]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.RestrictedPrincipalCycle
