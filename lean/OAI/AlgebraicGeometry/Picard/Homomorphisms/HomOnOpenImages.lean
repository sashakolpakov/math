import OAI.AlgebraicGeometry.Picard.Homomorphisms.LocalHomSections

/-! # Hom On Open Images -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.HomOnOpenImages

noncomputable section

/-! A module morphism restricted to an open immersion is a section of
internal Hom on its image, with the actual local-map coordinates retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules)

def moduleHomOnImageEquiv : (M.restrict f ⟶ N.restrict f) ≃
    Γ(InternalHom.Construction.moduleInternalHom M N, f ''ᵁ (⊤ : X.Opens)) :=
  (GlobalHomSections.Construction.moduleHomGlobalSectionEquiv (M.restrict f) (N.restrict f)).trans
    (InternalHomRestriction.Construction.localLinearHomRestrictEquiv f M N ⊤).symm

theorem moduleHomOnImageEquiv_restrict (b : M.restrict f ⟶ N.restrict f) :
    InternalHomRestriction.Construction.localLinearHomRestrict f M N ⊤ (moduleHomOnImageEquiv f M N b) =
      GlobalHomSections.Construction.moduleHomGlobalSection (M.restrict f) (N.restrict f) b :=
  (InternalHomRestriction.Construction.localLinearHomRestrictEquiv f M N ⊤).apply_symm_apply _

theorem moduleHomOnImageEquiv_coordinate (b : M.restrict f ⟶ N.restrict f) (U : X.Opens) :
    (moduleHomOnImageEquiv f M N b).val.app (op (Over.mk (f.opensFunctor.map U.leTop))) =
      b.app U := by
  have h := congrArg (fun a : Γ(InternalHom.Construction.moduleInternalHom (M.restrict f) (N.restrict f), ⊤) =>
    a.val.app (op (Over.mk U.leTop))) (moduleHomOnImageEquiv_restrict f M N b)
  exact h

omit [IsOpenImmersion f] in
theorem internalHom_coordinate_transport {W U V : Y.Opens}
    (a : Γ(InternalHom.Construction.moduleInternalHom M N, W)) (hU : U ≤ W) (hV : V ≤ W) (h : U = V) :
    a.val.app (op (Over.mk (homOfLE hU))) =
      M.presheaf.map (eqToHom h.symm).op ≫
        a.val.app (op (Over.mk (homOfLE hV))) ≫ N.presheaf.map (eqToHom h).op := by
  cases h
  simp only [eqToHom_refl, op_id]
  have he := congrArg₂
    (fun (r : End (M.presheaf.obj (op U))) (s : End (N.presheaf.obj (op U))) =>
      r ≫ a.val.app (op (Over.mk (homOfLE hV))) ≫ s)
    (M.presheaf.map_id (op U)) (N.presheaf.map_id (op U))
  exact ((he.trans (Category.id_comp _)).trans (Category.comp_id _)).symm

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.HomOnOpenImages
