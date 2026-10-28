import OAI.AlgebraicGeometry.FormalGeometry.Completion.StalkFlat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Stalk Chart Projection -/

namespace OAI.RepresentationTheory.Theta.Geometric.StalkChartProjection

noncomputable section

/-! The local-ring map of an actual smooth chart agrees with the
original scheme projection after the affine chart inclusion. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem stalkChart_projection {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hx : x ∈ V) (e : V ≤ f ⁻¹ᵁ U) :
    Spec.map (f.appLE U V e ≫ X.presheaf.germ V x hx) ≫ hU.fromSpec =
      X.fromSpecStalk x ≫ f := by
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e,
    ← Category.assoc]
  exact congrArg (· ≫ f) (hV.fromSpecStalk_eq_fromSpecStalk hx)

end

end OAI.RepresentationTheory.Theta.Geometric.StalkChartProjection
