import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.LineBundleSectionFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.OpenPullbackSectionInjectivity

/-! # Line Bundle Section Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LineBundleSectionFiniteness

noncomputable section

/-! Proper integral schemes over Noetherian affine bases have finite global sections for every actual line bundle, proved by pullback to the constructed projective Chow modification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem proper_integral_lineBundle_sections_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of R)) [IsProper f] (L : Line.Bundles.LineBundle X) :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor f).obj L.sheaf) := by
  let D := Chow.Modification.ChowModification.build f
  have : Nonempty D.cover.common := D.cover.common_nonempty
  have : IsIso (D.projection ∣_ D.cover.common) := D.isIso_restrict
  have hf : Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (D.projection ≫ f)).obj
      (L.pullback D.projection).sheaf) :=
    D.lineBundleSections_finite (L.pullback D.projection)
  have htarget : Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor f).obj
      ((Scheme.Modules.pushforward D.projection).obj (L.pullback D.projection).sheaf)) :=
    Module.Finite.equiv (Coefficient.GlobalSectionsPushforward.schemeGlobalSectionsPushforwardIso D.projection f
      (L.pullback D.projection).sheaf).symm
  have : Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor f).obj
      ((Scheme.Modules.pullback D.projection ⋙ Scheme.Modules.pushforward D.projection).obj L.sheaf)) :=
    htarget
  let a := ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor f).map
    ((Scheme.Modules.pullbackPushforwardAdjunction D.projection).unit.app L.sheaf)).hom
  have ha : Function.Injective a :=
    Common.OpenPullbackSectionInjectivity.lineBundle_pullbackUnit_top_injective_of_common_open D.projection L D.cover.common
  exact Module.Finite.of_injective a ha

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LineBundleSectionFiniteness
