import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.CenterRestriction

/-! # Etale Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent

noncomputable section

/-! Actual canonical global component centers commute with étale base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.center_comap_etale {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (g : Y ⟶ X) [Etale g]
    (B : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas (g ≫ f) (J.comap g) n) :
    A.center.comap g = B.center := by
  apply Finite.OpenIdealSheafUniqueness.Construction.idealSheaf_eq_of_open_affine_restrictions (fun i => Spec (B.rings i)) B.map B.cover
  intro i
  rw [← Scheme.IdealSheafData.comap_comp, B.center_restrict i]
  apply A.center_restrict_etale (B.rings i) (B.map i ≫ g)
  · rw [Category.assoc]
    exact B.ground i
  · rw [Scheme.IdealSheafData.comap_comp]
    exact B.ideal_eq i

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent
