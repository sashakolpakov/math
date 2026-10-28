import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenDiagram
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Open Intersection Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.OpenIntersectionPullback

noncomputable section

/-! The intersection of two actual open subfamilies is their
pullback over the original family, also in the category over the base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme} (X : Over S)

theorem familyOpenIntersection_isPullback (V W : X.left.Opens) :
    IsPullback (Affine.OpenDiagram.familyOpenMap X (show V ⊓ W ≤ V from inf_le_left))
      (Affine.OpenDiagram.familyOpenMap X (show V ⊓ W ≤ W from inf_le_right))
      (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X V) (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X W) := by
  apply IsPullback.of_map_of_faithful (Over.forget S)
  exact isPullback_opens_inf V W

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.OpenIntersectionPullback
