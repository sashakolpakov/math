import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.PointMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.CycleMoving

/-! # Simultaneous Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.SimultaneousMoving

noncomputable section

/-! In any dimension, a divisor can be moved to meet two prescribed
cycles properly while avoiding any additional finite set of points. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

theorem move (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (T : Finset X.carrier) (a : X.RationalDimensionCycle 1) (b c : X.RationalDimensionCycle q) :
    ∃ a' : X.RationalDimensionCycle 1, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a' ∧
      CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 q a' b ∧ CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 q a' c ∧
      ∀ D ∈ a'.support, ∀ x ∈ T, x ∉ (D.val : Set X.carrier) := by
  let U := b.support ∪ c.support
  let S := T ∪ U.image (fun B => CycleClass.Thom.IntersectionGeometry.supportPoint B.val)
  obtain ⟨a', ha', hav⟩ := PointMoving.move X m S a
  have hp (D : X.DimensionCycleSupport 1) (hD : D ∈ a'.support)
      (B : X.DimensionCycleSupport q) (hB : B ∈ U) : ¬ B.val ≤ D.val := by
    intro hBD
    exact hav D hD (CycleClass.Thom.IntersectionGeometry.supportPoint B.val)
      (Finset.mem_union_right T (Finset.mem_image.mpr ⟨B, hB, rfl⟩))
      (hBD (B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).mem)
  exact ⟨a', ha', CycleMoving.of_avoiding X m q a' b
    (fun D hD B hB => hp D hD B (Finset.mem_union_left _ hB)),
    CycleMoving.of_avoiding X m q a' c
    (fun D hD B hB => hp D hD B (Finset.mem_union_right _ hB)),
    fun D hD x hx => hav D hD x (Finset.mem_union_left _ hx)⟩

theorem move_pair (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle 1) (b c : X.RationalDimensionCycle q) :
    ∃ a' : X.RationalDimensionCycle 1, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a' ∧
      CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 q a' b ∧ CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 q a' c := by
  obtain ⟨a', ha', hb, hc, _⟩ := move X m q ∅ a b c
  exact ⟨a', ha', hb, hc⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.SimultaneousMoving
