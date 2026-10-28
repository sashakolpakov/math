import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Morphism Restricted Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.MorphismRestrictedPoints

noncomputable section

/-! Equality of pulled-back morphisms is detected by points over test schemes above the new base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem pullback_map_eq_iff_restrictedPoints
    {S T : Scheme.{u}} {X Y : Over S} (b : T ⟶ S) (f g : X ⟶ Y) :
    (Over.pullback b).map f = (Over.pullback b).map g ↔
      ∀ (U : Over T) (z : (Over.map b).obj U ⟶ X), z ≫ f = z ≫ g := by
  let a := Over.mapPullbackAdj b
  constructor
  · intro h U z
    apply (a.homEquiv U Y).injective
    rw [a.homEquiv_naturality_right, a.homEquiv_naturality_right, h]
  · intro h
    let U := (Over.pullback b).obj X
    let z := (a.homEquiv U X).symm (𝟙 U)
    have H := congrArg (a.homEquiv U Y) (h U z)
    rw [a.homEquiv_naturality_right, a.homEquiv_naturality_right] at H
    have hz : a.homEquiv U X z = 𝟙 U := (a.homEquiv U X).apply_symm_apply (𝟙 U)
    rw [hz, Category.id_comp, Category.id_comp] at H
    exact H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.MorphismRestrictedPoints
