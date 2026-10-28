import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.CycleMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportStalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportPrime

/-! # Support Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.SupportCycle

noncomputable section

/-! The actual finite proper intersection of a divisor and an arbitrary
support, with its coefficients and the actual supports inside each input. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m r : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport r)

def cycle : X.RationalDimensionCycle (1 + r) :=
  Supports.ProperCycle.intersectionBilinear X m 1 r (Finsupp.single D 1) (Finsupp.single W 1)

include m

theorem proper (hDW : ¬ W.val ≤ D.val) : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 r (Finsupp.single D 1) (Finsupp.single W 1) := by
  apply CycleMoving.of_avoiding X m r
  intro B hB A hA
  have hBD : B = D := by simpa using hB
  have hAW : A = W := by simpa using hA
  subst B
  subst A
  exact hDW

theorem coefficient (hDW : ¬ W.val ≤ D.val) (A : X.DimensionCycleSupport (1 + r)) :
    cycle X m r D W A = CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val W.val A.val := by
  have hc := Supports.ProperCycle.intersectionBilinear_isProper X m 1 r (Finsupp.single D 1) (Finsupp.single W 1)
    (proper X m r D W hDW)
  simpa only [cycle, Finsupp.sum_single_index, zero_mul, mul_zero, one_mul] using hc.2 A

theorem support_subset (hDW : ¬ W.val ≤ D.val) (A : X.DimensionCycleSupport (1 + r))
    (hA : A ∈ (cycle X m r D W).support) : A.val ≤ D.val ∧ A.val ≤ W.val := by
  have hn : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val W.val A.val ≠ 0 :=
    (coefficient X m r D W hDW A) ▸ Finsupp.mem_support_iff.mp hA
  have hx : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ (D.val : Set X.carrier) ∩ (W.val : Set X.carrier) := by
    by_contra h
    exact hn (dite_eq_right h)
  exact ⟨(Supports.supportPoint_mem_iff_subset
    (⟨(D.val : Set X.carrier), D.val.isClosed⟩ : Closeds X.carrier) A.val).mp hx.1,
    (Supports.supportPoint_mem_iff_subset
    (⟨(W.val : Set X.carrier), W.val.isClosed⟩ : Closeds X.carrier) A.val).mp hx.2⟩

theorem inner_coheight (hDW : ¬ W.val ≤ D.val) (A : X.DimensionCycleSupport (1 + r))
    (hA : A ∈ (cycle X m r D W).support) :
    Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint (NestedSupport.innerSupport X.carrier A.val W.val
      (support_subset X m r D W hDW A hA).2)) = 1 := by
  rw [NestedSupport.innerSupport_point]
  let A' : X.DimensionCycleSupport (r + 1) := ⟨A.val, by rw [A.property]; omega⟩
  exact AdjacentSupportStalk.coheight_one X m r W A' _

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.SupportCycle
