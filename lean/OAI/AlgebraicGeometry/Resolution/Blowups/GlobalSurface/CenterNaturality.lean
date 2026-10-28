import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.CenterEtaleRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalGlobalCoefficientBound

/-! # Center Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Fixed-level canonical surface centers commute with actual global étale restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_comap_etale
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (ℓ : ℕ)
    (ha : ∀ i, (A.choice i).HasBound (ℓ + 1)) (hdA : ∀ i, ringKrullDim (A.rings i) ≤ 2)
    (hlevel : (n + 1).factorial ≤ ℓ + 1)
    {Y : Scheme} (g : Y ⟶ X) [Etale g]
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas (g ≫ f) (J.comap g) n)
    (hb : ∀ i, (B.choice i).HasBound (ℓ + 1)) (hdB : ∀ i, ringKrullDim (B.rings i) ≤ 2) :
    (A.surfaceCenter ℓ ha hdA hlevel).comap g = B.surfaceCenter ℓ hb hdB hlevel := by
  apply Finite.OpenIdealSheafUniqueness.Construction.idealSheaf_eq_of_open_affine_restrictions (fun i => Spec (B.rings i)) B.map B.cover
  intro i
  rw [← Scheme.IdealSheafData.comap_comp, B.surfaceCenter_restrict ℓ hb hdB hlevel i]
  apply A.surfaceCenter_restrict_etale ℓ ha hdA hlevel (B.rings i) (B.map i ≫ g)
  · rw [Category.assoc]
    exact B.ground i
  · rw [Scheme.IdealSheafData.comap_comp]
    exact B.ideal_eq i
  · exact hdB i

end

end OAI.AlgebraicGeometry.Resolution.Blowups
