import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Cycle

/-! # Cycle Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.CycleSupport

noncomputable section

/-! Every nonzero component of a smooth inverse-image cycle comes
from one of the original supports and is contained in its inverse image. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
  (m n p : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

include m n in
theorem origin (a : Y.RationalDimensionCycle p) (A : X.DimensionCycleSupport p)
    (hA : A ∈ (Cycle.flatMap f p a).support) :
    ∃ B ∈ a.support, f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val ∧
      (A.val : Set X.carrier) ⊆ f.left ⁻¹' (B.val : Set Y.carrier) := by
  have hn := Finsupp.mem_support_iff.mp hA
  rw [Cycle.flatMap_apply f p m n, Finsupp.sum] at hn
  obtain ⟨B, hB, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have he : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val := by
    by_contra h
    simp only [ite_eq_right h, mul_zero, ne_eq, not_true_eq_false] at hb
  refine ⟨B, hB, he, ?_⟩
  apply (Supports.supportPoint_mem_iff_subset (Cycle.support f p B) A.val).mp
  change f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) ∈ (B.val : Set Y.carrier)
  rw [he]
  exact (B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).mem

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.CycleSupport
