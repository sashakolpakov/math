/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.ClosedImmersion.SourceOpen
import OAI.CategoryTheory.ConcreteCategory.Notation

/-! # Source Open Is -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Restricting the source of a closed immersion without losing closedness

-/

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

/-- The actual immersion image formula, with structure-map compatibility bundled in `i`. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion_of_comm (X Y : Over (Spec ↧ℂ))
    (i : Y ⟶ X) [IsImmersion i.left] [LocallyOfFiniteType X.hom] :
    Set.range (ComplexPoint.Basic.Point.map i) =
      (ComplexPoint.Basic.Point.underlying : ComplexPoint.Basic.ComplexSchemePoint X → X.left) ⁻¹' Set.range i.left := by
  let : LocallyOfFiniteType Y.hom := by
    rw [← i.w]
    infer_instance
  exact ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion X i

end

end OAI.AlgebraicGeometry
