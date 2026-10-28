import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalGlobalCoefficientBound

/-! # Bound Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A coefficient bound transports across an actual étale comparison with separately named structure map and ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.hasBound_transport_etale
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas g K n)
    (q : Y ⟶ X) [Etale q] (hg : q ≫ f = g) (hK : J.comap q = K)
    (m : ℕ) (hbound : ∀ i, (A.choice i).HasBound m) : ∀ i, (B.choice i).HasBound m := by
  subst g
  subst K
  exact A.hasBound_comap_etale m hbound q B

end

end OAI.AlgebraicGeometry.Resolution.Blowups
