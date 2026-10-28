import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionPullback

/-! # Section Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionPullbackComposition

noncomputable section

/-! Pulling a regular function to a specified subopen commutes with composition and open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem openSectionPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (hg : V ≤ g ⁻¹ᵁ U) (hf : W ≤ f ⁻¹ᵁ V) (hfg : W ≤ (f ≫ g) ⁻¹ᵁ U) (r : Γ(Z, U)) :
    SectionPullback.openSectionPullback f V W hf (SectionPullback.openSectionPullback g U V hg r) =
      SectionPullback.openSectionPullback (f ≫ g) U W hfg r :=
  ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE f g U V W hg hf) r

theorem openSectionPullback_congr {f g : X ⟶ Y} (he : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) (r : Γ(Y, U)) :
    SectionPullback.openSectionPullback f U V hf r = SectionPullback.openSectionPullback g U V hg r := by
  subst g
  rfl

theorem openSectionPullback_open_top (U : X.Opens) (V : X.Opens) (h : U ≤ V)
    (hU : ⊤ ≤ U.ι ⁻¹ᵁ V) (r : Γ(X, V)) :
    SectionPullback.openSectionPullback U.ι V ⊤ hU r =
      U.topIso.inv (X.presheaf.map (homOfLE h).op r) := by
  have hs : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  have he := Scheme.Hom.map_appLE U.ι U.ι_preimage_self.ge (homOfLE h).op
  exact (ConcreteCategory.congr_hom he r).symm.trans
    (congrArg (fun z => z (X.presheaf.map (homOfLE h).op r)) hs)

theorem openSectionPullback_open_self (U : X.Opens) (r : Γ(X, U)) :
    SectionPullback.openSectionPullback U.ι U ⊤ U.ι_preimage_self.ge r = U.topIso.inv r := by
  change U.ι.appLE U ⊤ U.ι_preimage_self.ge r = _
  rw [Scheme.Opens.ι_appLE]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionPullbackComposition
