import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsomorphismOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ParameterPoints

/-! # Isomorphism Open Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphismOpenParameters

noncomputable section

/-! The isomorphism condition on a proper family morphism is represented by an actual open parameter subscheme on all tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) {X Y : Over M.left}
variable [IsProper X.hom] [Flat X.hom] [IsProper Y.hom] [IsLocallyNoetherian Y.left]
variable (j : X ⟶ Y)

def isomorphismOpenParameter : Over S := Open.ParameterPoints.openParameterScheme M (HilbertConstruction.Over.IsomorphismOpen.overIsomorphismOpen j)

def isomorphismOpenParameterPointEquiv (T : Over S) :
    (T ⟶ isomorphismOpenParameter M j) ≃ {c : T ⟶ M // IsIso ((Over.pullback c.left).map j)} :=
  (Open.ParameterPoints.openParameterPointEquiv M (HilbertConstruction.Over.IsomorphismOpen.overIsomorphismOpen j) T).trans
    { toFun := fun c => ⟨c.val, (HilbertConstruction.Over.IsomorphismOpen.overIsomorphismOpen_pullback_iff j c.val.left).mpr c.property⟩
      invFun := fun c => ⟨c.val, (HilbertConstruction.Over.IsomorphismOpen.overIsomorphismOpen_pullback_iff j c.val.left).mp c.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphismOpenParameters
