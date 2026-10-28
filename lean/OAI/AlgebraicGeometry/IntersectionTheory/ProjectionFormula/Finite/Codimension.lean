import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualAvoidance
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ResidueDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardComposition

/-! # Codimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Codimension

noncomputable section

/-! Finite projections between smooth schemes of equal dimension
preserve support codimension, including the lower bound on residual supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
  (f : X.toOver ⟶ Y.toOver) [IsFinite f.left] (m : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension m Y.structureMap]

abbrev map : X.carrier ⟶ Y.carrier := f.left

include m in
theorem image (W : IrreducibleCloseds X.carrier) :
    Y.supportCodimension (ProperCycleLinearity.imageSupport f W) = X.supportCodimension W := by
  have hd := PushforwardComposition.Grading.support_dimension_eq_of_degree f W
    (Nat.ne_of_gt (ResidueDegree.positive f.left (CycleClass.Thom.IntersectionGeometry.supportPoint W)))
  have hx := Grading.supportDimension_add_codimension X m W
  have hy := Grading.supportDimension_add_codimension Y m (ProperCycleLinearity.imageSupport f W)
  omega

include m in
theorem preimage (W C : IrreducibleCloseds X.carrier)
    (hC : (C : Set X.carrier) ⊆ f.left ⁻¹' (f.left '' (W : Set X.carrier))) :
    X.supportCodimension W ≤ X.supportCodimension C := by
  have hi : ProperCycleLinearity.imageSupport f C ≤ ProperCycleLinearity.imageSupport f W := by
    change (ProperCycleLinearity.imageSupport f C : Set Y.carrier) ⊆ ProperCycleLinearity.imageSupport f W
    rw [ProperCycleLinearity.imageSupport_eq_image, ProperCycleLinearity.imageSupport_eq_image]
    rintro y ⟨x, hx, rfl⟩
    exact hC hx
  have hd := (Supports.codimension_strictAnti Y m).antitone hi
  rwa [image f m, image f m] at hd

theorem residual_subset (W : IrreducibleCloseds X.carrier) :
    (ResidualAvoidance.Projection.residual (map f) W : Set X.carrier) ⊆
      f.left ⁻¹' (f.left '' (W : Set X.carrier)) := by
  apply closure_minimal Set.sdiff_subset
  exact (f.left.isClosedMap _ W.isClosed).preimage f.left.continuous

include m in
theorem residual (W C : IrreducibleCloseds X.carrier)
    (hC : (C : Set X.carrier) ⊆ ResidualAvoidance.Projection.residual (map f) W) :
    X.supportCodimension W ≤ X.supportCodimension C :=
  Projection.preimage f m W C (hC.trans (residual_subset f W))

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Codimension
