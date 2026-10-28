import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.LineBundleLocalization

/-! # Open Line Bundle Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenLineBundleLocalization

noncomputable section

/-! Global line-bundle sections localize on inverse images of principal affine base opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem basicOpenGlobalAlgebra_isLocalization (S : Scheme.{u}) [IsAffine S] (r : Γ(S, ⊤)) :
    IsLocalization.Away r (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.basicOpen r).ι) := by
  change @IsLocalization.Away Γ(S, ⊤) _ r Γ((S.basicOpen r).toScheme, ⊤) _
    (S.basicOpen r).ι.appTop.hom.toAlgebra
  exact Γ_restrict_isLocalization S r

theorem lineBundle_sections_localize_on_base_basicOpen
    {X S : Scheme.{u}} [IsAffine S] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ S) (L : Line.Bundles.LineBundle X) (r : Γ(S, ⊤)) :
    IsLocalizedModule.Away r
      ((Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap (f ⁻¹ᵁ S.basicOpen r).ι f.appTop.hom L.sheaf).app
        (.op ⊤)).hom := by
  have : IsAffine (S.basicOpen r).toScheme := (isAffineOpen_top S).basicOpen r
  have : IsLocalization.Away r (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.basicOpen r).ι) :=
    basicOpenGlobalAlgebra_isLocalization S r
  exact Flat.LineBundleLocalization.localized_lineBundle_section_pullback (isPullback_morphismRestrict f (S.basicOpen r)).flip L
    (Submonoid.powers r)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenLineBundleLocalization
