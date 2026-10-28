import OAI.AlgebraicGeometry.Picard.Homomorphisms.HomOnOpenImages

/-! # Hom Image Restriction -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.HomImageRestriction

noncomputable section

/-! Restricting a local module morphism restricts its internal-Hom
section on the corresponding open image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsOpenImmersion f] [IsOpenImmersion g] (L M : Z.Modules)

def compositeRestrictedModuleHom (b : L.restrict g ⟶ M.restrict g) :
    L.restrict (f ≫ g) ⟶ M.restrict (f ≫ g) :=
  (Scheme.Modules.restrictFunctorComp f g).hom.app L ≫
    (Scheme.Modules.restrictFunctor f).map b ≫ (Scheme.Modules.restrictFunctorComp f g).inv.app M

def compositeImageInclusion : (f ≫ g) ''ᵁ (⊤ : X.Opens) ⟶ g ''ᵁ (⊤ : Y.Opens) :=
  homOfLE ((Scheme.Hom.comp_image f g ⊤).le.trans (g.image_mono le_top))

theorem moduleHomOnImageEquiv_comp (b : L.restrict g ⟶ M.restrict g) :
    HomOnOpenImages.Construction.moduleHomOnImageEquiv (f ≫ g) L M (compositeRestrictedModuleHom f g L M b) =
      (InternalHom.Construction.moduleInternalHom L M).presheaf.map (compositeImageInclusion f g).op
        (HomOnOpenImages.Construction.moduleHomOnImageEquiv g L M b) := by
  apply InternalHomRestriction.Construction.localLinearHomRestrict_injective (f ≫ g) L M ⊤
  rw [HomOnOpenImages.Construction.moduleHomOnImageEquiv_restrict]
  apply Subtype.ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.ext
  intro m
  let V := W.unop.left
  let a := HomOnOpenImages.Construction.moduleHomOnImageEquiv g L M b
  let j₁ := (f ≫ g).opensFunctor.map W.unop.hom ≫ compositeImageInclusion f g
  let j₂ := g.opensFunctor.map (f ''ᵁ V).leTop
  have hV : (f ≫ g) ''ᵁ V = g ''ᵁ (f ''ᵁ V) := Scheme.Hom.comp_image f g V
  have hc := HomOnOpenImages.Construction.internalHom_coordinate_transport L M a (leOfHom j₁) (leOfHom j₂) hV
  have hb := HomOnOpenImages.Construction.moduleHomOnImageEquiv_coordinate g L M b (f ''ᵁ V)
  change a.val.app (op (Over.mk j₂)) = b.app (f ''ᵁ V) at hb
  change M.presheaf.map (eqToHom hV).op
      (b.app (f ''ᵁ V) (L.presheaf.map (eqToHom hV.symm).op m)) =
    a.val.app (op (Over.mk j₁)) m
  have hv := ConcreteCategory.congr_hom hc m
  change a.val.app (op (Over.mk j₁)) m =
    M.presheaf.map (eqToHom hV).op
      (a.val.app (op (Over.mk j₂)) (L.presheaf.map (eqToHom hV.symm).op m)) at hv
  exact (hv.trans (congrArg (fun q => M.presheaf.map (eqToHom hV).op
    (q (L.presheaf.map (eqToHom hV.symm).op m))) hb)).symm

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.HomImageRestriction
