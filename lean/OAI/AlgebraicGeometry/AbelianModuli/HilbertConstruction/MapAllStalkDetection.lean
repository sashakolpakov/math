import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StalkPullbackDetection

/-! # Map All Stalk Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MapAllStalkDetection

noncomputable section

/-! All local-ring points detect scheme morphisms, without noetherian or reduced hypotheses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem schemeMap_eq_of_allStalkPoints {X Y : Scheme.{u}} (f g : X ⟶ Y)
    (h : ∀ x : X, X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) : f = g := by
  have he : ∀ x : X, f x = g x := by
    intro x
    have e := congrArg (fun q : Spec (X.presheaf.stalk x) ⟶ Y => q (IsLocalRing.closedPoint _)) (h x)
    change f (X.fromSpecStalk x (IsLocalRing.closedPoint _)) =
      g (X.fromSpecStalk x (IsLocalRing.closedPoint _)) at e
    rw [Scheme.fromSpecStalk_closedPoint] at e
    exact e
  have hb : f.base = g.base := by ext x; exact he x
  have hs : ∀ x : X, f.stalkMap x =
      Y.presheaf.stalkSpecializes (Inseparable.of_eq (he x).symm).specializes ≫ g.stalkMap x := by
    intro x
    apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecStalk (f x)), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact h x
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  apply SheafedSpace.hom_stalk_ext _ _ hb
  intro x
  exact hs x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MapAllStalkDetection
