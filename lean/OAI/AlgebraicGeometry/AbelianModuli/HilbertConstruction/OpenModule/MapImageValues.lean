import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRecovery

/-! # Map Image Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapImageValues

noncomputable section

/-! On the image of an open set, ambient map values are the original local map components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

theorem moduleRestrictionUnit_image (M : Y.Modules) (W : X.Opens) :
    ((Scheme.Modules.restrictAdjunction f).unit.app M).app (f ''ᵁ W) =
      (M.restrict f).presheaf.map (eqToHom (f.preimage_image_eq W)).op := by
  change M.presheaf.map (homOfLE (f.image_preimage_le (f ''ᵁ W))).op =
    M.presheaf.map (f.opensFunctor.map (eqToHom (f.preimage_image_eq W))).op
  congr 1

theorem openModuleMapValue_image {M N : Y.Modules}
    (φ : M.restrict f ⟶ N.restrict f) (W : X.Opens) (s : Γ(M, f ''ᵁ W)) :
    MapValues.openModuleMapValue f φ (f ''ᵁ W) (f.image_le_opensRange W) s = φ.app W s := by
  let : IsIso (((Scheme.Modules.restrictAdjunction f).unit.app N).app (f ''ᵁ W)) :=
    MapValues.moduleRestrictionUnit_app_isIso f N (f ''ᵁ W) (f.image_le_opensRange W)
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictAdjunction f).unit.app N).app (f ''ᵁ W))).1
  rw [MapRecovery.openModuleMapValue_spec]
  change φ.app (f ⁻¹ᵁ f ''ᵁ W)
    (((Scheme.Modules.restrictAdjunction f).unit.app M).app (f ''ᵁ W) s) =
      ((Scheme.Modules.restrictAdjunction f).unit.app N).app (f ''ᵁ W) (φ.app W s)
  rw [moduleRestrictionUnit_image, moduleRestrictionUnit_image]
  exact ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (eqToHom (f.preimage_image_eq W)).op) s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapImageValues
