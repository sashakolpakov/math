import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LineBundleSectionFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SpecGlobalSectionIdentities
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Integral Affine Image Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralAffineImageFiniteness

noncomputable section

/-! Proper integral line-bundle direct images have finite sections on affine Noetherian targets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem proper_integral_affine_directImage_sections_finite
    {X S : Scheme.{u}} [IsIntegral X] [IsAffine S] [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] (L : Line.Bundles.LineBundle X) :
    Module.Finite Γ(S, ⊤) Γ((pushforward f).obj L.sheaf, ⊤) := by
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  have : Module.Finite Γ(S, ⊤)
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (f ≫ S.toSpecΓ)).obj L.sheaf) :=
    LineBundleSectionFiniteness.proper_integral_lineBundle_sections_finite (f ≫ S.toSpecΓ) L
  exact Module.Finite.equiv
    ((Coefficient.GlobalSectionsPushforward.schemeGlobalSectionsPushforwardIso f S.toSpecΓ L.sheaf).symm.trans
      (SpecGlobalSectionIdentities.schemeGlobalSectionsToSpecIso ((pushforward f).obj L.sheaf)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralAffineImageFiniteness
