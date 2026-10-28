import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralAffineImageFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LineBundleImage

/-! # Integral Restricted Image Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralRestrictedImageFiniteness

noncomputable section

/-! Finite sections of restricted proper direct images over nonempty affine neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite

universe u

theorem proper_integral_restricted_directImage_sections_finite
    {X S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] (L : Line.Bundles.LineBundle X)
    (U : S.Opens) (hU : IsAffineOpen U) [Nonempty (f ⁻¹ᵁ U)] :
    Module.Finite Γ(U.toScheme, ⊤)
      Γ(((pushforward f).obj L.sheaf).restrict U.ι, ⊤) := by
  let V := f ⁻¹ᵁ U
  let q := f ∣_ U
  have : IsAffine U.toScheme := hU
  have : Nonempty V.toScheme := inferInstanceAs (Nonempty V)
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : Module.Finite Γ(U.toScheme, ⊤)
      Γ((pushforward q).obj (L.pullback V.ι).sheaf, ⊤) :=
    IntegralAffineImageFiniteness.proper_integral_affine_directImage_sections_finite q (L.pullback V.ι)
  let e : (((pushforward f).obj L.sheaf).restrict U.ι) ≅
      (pushforward q).obj (L.pullback V.ι).sheaf :=
    Open.RestrictionPushforward.restrictPushforwardIsoOfIsPullbackApp f q V.ι U.ι
      (isPullback_morphismRestrict f U) L.sheaf ≪≫
        (pushforward q).mapIso ((restrictFunctorIsoPullback V.ι).app L.sheaf)
  let eΓ : Γ(((pushforward f).obj L.sheaf).restrict U.ι, ⊤) ≃ₗ[Γ(U.toScheme, ⊤)]
      Γ((pushforward q).obj (L.pullback V.ι).sheaf, ⊤) :=
    ((SheafOfModules.evaluation U.toScheme.ringCatSheaf (op ⊤)).mapIso e).toLinearEquiv
  exact Module.Finite.equiv eΓ.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralRestrictedImageFiniteness
