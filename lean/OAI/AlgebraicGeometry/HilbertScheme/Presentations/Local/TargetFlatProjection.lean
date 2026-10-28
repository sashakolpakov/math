import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.LocalSpectra

/-! # Target Flat Projection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.TargetFlatProjection

noncomputable section

/-! A family flat over its base remains flat over the base local ring
after localizing its target at any point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ B) (y : Y)

def localTargetOverBaseStalkMap :
    pullback (Y.fromSpecStalk y) f ⟶ Spec (B.presheaf.stalk (q y)) :=
  pullback.fst (Y.fromSpecStalk y) f ≫ Spec.map (q.stalkMap y)

theorem localTargetOverBaseStalkMap_comp :
    localTargetOverBaseStalkMap f q y ≫ B.fromSpecStalk (q y) =
      pullback.snd (Y.fromSpecStalk y) f ≫ f ≫ q := by
  rw [localTargetOverBaseStalkMap, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← Category.assoc, pullback.condition, Category.assoc]

theorem localTargetOverBaseStalkMap_flat [Flat (f ≫ q)] :
    Flat (localTargetOverBaseStalkMap f q y) := by
  let : Flat (Y.fromSpecStalk y) := Presentations.Flat.LocalSpectra.flat_fromSpecStalk Y y
  have h : Flat (localTargetOverBaseStalkMap f q y ≫ B.fromSpecStalk (q y)) := by
    rw [localTargetOverBaseStalkMap_comp]
    exact inferInstanceAs (Flat (pullback.snd (Y.fromSpecStalk y) f ≫ (f ≫ q)))
  exact Presentations.Flat.LocalSpectra.flat_of_comp_mono (localTargetOverBaseStalkMap f q y) (B.fromSpecStalk (q y))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.TargetFlatProjection
