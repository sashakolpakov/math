import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapImageValues

/-! # Map Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapComposition

noncomputable section

/-! Ambient values are unchanged by restricting a local module map to a smaller open subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsOpenImmersion f] [IsOpenImmersion g] {M N : Z.Modules}

def restrictOpenModuleMap (φ : M.restrict g ⟶ N.restrict g) :
    M.restrict (f ≫ g) ⟶ N.restrict (f ≫ g) :=
  (Scheme.Modules.restrictFunctorComp f g).hom.app M ≫
    (Scheme.Modules.restrictFunctor f).map φ ≫ (Scheme.Modules.restrictFunctorComp f g).inv.app N

theorem restrictOpenModuleMap_app (φ : M.restrict g ⟶ N.restrict g) (W : X.Opens) :
    (restrictOpenModuleMap f g φ).app W =
      M.presheaf.map (eqToHom (Scheme.Hom.comp_image f g W).symm).op ≫
        φ.app (f ''ᵁ W) ≫ N.presheaf.map (eqToHom (Scheme.Hom.comp_image f g W)).op := rfl

theorem openModuleMapValue_comp_image (φ : M.restrict g ⟶ N.restrict g)
    (W : X.Opens) (s : Γ(M, (f ≫ g) ''ᵁ W)) :
    MapValues.openModuleMapValue (f ≫ g) (restrictOpenModuleMap f g φ) ((f ≫ g) ''ᵁ W)
      ((f ≫ g).image_le_opensRange W) s =
      MapValues.openModuleMapValue g φ ((f ≫ g) ''ᵁ W)
        ((Scheme.Hom.comp_image f g W).trans_le (g.image_le_opensRange (f ''ᵁ W))) s := by
  let h := (Scheme.Hom.comp_image f g W).symm.le
  let eN := N.presheaf.mapIso (eqToIso (Scheme.Hom.comp_image f g W).symm).op
  have : IsIso (homOfLE h) := homOfLE_isIso_of_eq h (Scheme.Hom.comp_image f g W).symm
  have : IsIso (N.presheaf.map (homOfLE h).op) := N.presheaf.map_isIso _
  apply (ConcreteCategory.bijective_of_isIso (N.presheaf.map (homOfLE h).op)).1
  rw [MapImageValues.openModuleMapValue_image]
  have hn := MapValues.openModuleMapValue_natural g φ h
    ((Scheme.Hom.comp_image f g W).trans_le (g.image_le_opensRange (f ''ᵁ W)))
    (g.image_le_opensRange (f ''ᵁ W)) s
  rw [← hn, MapImageValues.openModuleMapValue_image, restrictOpenModuleMap_app]
  change eN.hom (eN.inv (φ.app (f ''ᵁ W)
    (M.presheaf.map (homOfLE h).op s))) = φ.app (f ''ᵁ W) (M.presheaf.map (homOfLE h).op s)
  exact ConcreteCategory.congr_hom eN.inv_hom_id _

theorem openModuleMapValue_comp (φ : M.restrict g ⟶ N.restrict g)
    (U : Z.Opens) (hU : U ≤ (f ≫ g).opensRange) :
    MapValues.openModuleMapValue (f ≫ g) (restrictOpenModuleMap f g φ) U hU =
      MapValues.openModuleMapValue g φ U (hU.trans (by
        rw [Scheme.Hom.opensRange_comp]
        exact g.image_le_opensRange f.opensRange)) := by
  have he : (f ≫ g) ''ᵁ (f ≫ g) ⁻¹ᵁ U = U :=
    ((f ≫ g).image_preimage_eq_opensRange_inf U).trans (inf_eq_right.mpr hU)
  have H : ∀ h₁ : (f ≫ g) ''ᵁ (f ≫ g) ⁻¹ᵁ U ≤ (f ≫ g).opensRange,
      ∀ h₂ : (f ≫ g) ''ᵁ (f ≫ g) ⁻¹ᵁ U ≤ g.opensRange,
      MapValues.openModuleMapValue (f ≫ g) (restrictOpenModuleMap f g φ)
        ((f ≫ g) ''ᵁ (f ≫ g) ⁻¹ᵁ U) h₁ =
      MapValues.openModuleMapValue g φ ((f ≫ g) ''ᵁ (f ≫ g) ⁻¹ᵁ U) h₂ := by
    intro h₁ h₂
    apply LinearMap.ext
    intro s
    exact openModuleMapValue_comp_image f g φ ((f ≫ g) ⁻¹ᵁ U) s
  have H' := (congrArg (fun V : Z.Opens => ∀ h₁ : V ≤ (f ≫ g).opensRange,
      ∀ h₂ : V ≤ g.opensRange,
      MapValues.openModuleMapValue (f ≫ g) (restrictOpenModuleMap f g φ) V h₁ =
        MapValues.openModuleMapValue g φ V h₂) he).mp H
  exact H' hU _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapComposition
