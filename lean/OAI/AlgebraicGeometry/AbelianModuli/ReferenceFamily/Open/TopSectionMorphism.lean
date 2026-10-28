import Mathlib.AlgebraicGeometry.Restrict

/-! # Top Section Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.TopSectionMorphism

noncomputable section

/-! The actual global sections of a map between open subschemes
agree with its original ambient section pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem openTopSection_morphism {X Y : Scheme.{0}} (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) (s : Γ(U.toScheme, ⊤)) :
    V.topIso.hom ((f.resLE U V h).appTop s) = f.appLE U V h (U.topIso.hom s) :=
  (ConcreteCategory.congr_hom (arrowResLEAppIso f U V h).hom.w s).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.TopSectionMorphism
