import OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHomMaps

/-! # Internal Hom Restriction -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHomRestriction

noncomputable section

/-! Restriction of local linear maps along an open immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

theorem opensOver_eq_of_left {U : Y.Opens} {V W : Over U} (h : V.left = W.left) : V = W := by
  cases V
  cases W
  cases h
  congr <;> exact Subsingleton.elim _ _

theorem opensOverPost_surjective (U : X.Opens) :
    Function.Surjective (Over.post (X := U) f.opensFunctor).obj := by
  intro W
  have hpre : f ⁻¹ᵁ W.left ≤ U := by
    calc
      f ⁻¹ᵁ W.left ≤ f ⁻¹ᵁ (f ''ᵁ U) := fun _ hx => (leOfHom W.hom) hx
      _ = U := f.preimage_image_eq U
  refine ⟨Over.mk (homOfLE hpre), opensOver_eq_of_left ?_⟩
  exact (f.image_preimage_eq_opensRange_inf W.left).trans
    (inf_eq_right.mpr ((leOfHom W.hom).trans (f.image_le_opensRange U)))

instance opensOverPost_isEquivalence (U : X.Opens) :
    (Over.post (X := U) f.opensFunctor).IsEquivalence := by
  have : (Over.post (X := U) f.opensFunctor).EssSurj :=
    ⟨fun W => by
      obtain ⟨V, hV⟩ := opensOverPost_surjective f U W
      exact ⟨V, ⟨eqToIso hV⟩⟩⟩
  exact {}

variable (M N : Y.Modules)

def localLinearHomRestrict (U : X.Opens)
    (a : Γ(InternalHom.Construction.moduleInternalHom M N, f ''ᵁ U)) :
    (ModuleHomSheaf.Construction.linearHomSubfunctor (M.restrict f) (N.restrict f)).toFunctor.obj (.op U) :=
  ⟨Functor.whiskerLeft (Over.post f.opensFunctor).op a.val,
    fun V r s => a.property ((Over.post f.opensFunctor).obj V) ((f.appIso V.left).inv r) s⟩

theorem localLinearHomRestrict_injective (U : X.Opens) :
    Function.Injective (localLinearHomRestrict f M N U) := by
  intro a b hab
  apply Subtype.ext
  let F := (Functor.whiskeringLeft (Over U)ᵒᵖ (Over (f ''ᵁ U))ᵒᵖ Ab).obj
    (Over.post f.opensFunctor).op
  exact F.map_injective (congrArg Subtype.val hab)

theorem localLinearHomRestrict_surjective (U : X.Opens) :
    Function.Surjective (localLinearHomRestrict f M N U) := by
  intro b
  let F := (Functor.whiskeringLeft (Over U)ᵒᵖ (Over (f ''ᵁ U))ᵒᵖ Ab).obj
    (Over.post f.opensFunctor).op
  let a : (presheafHom M.presheaf N.presheaf).obj (.op (f ''ᵁ U)) := F.preimage b.val
  have he : Functor.whiskerLeft (Over.post f.opensFunctor).op a = b.val :=
    F.map_preimage (X := (Over.forget (f ''ᵁ U)).op ⋙ M.presheaf)
      (Y := (Over.forget (f ''ᵁ U)).op ⋙ N.presheaf) b.val
  have ha : ModuleHomSheaf.Construction.IsLinearLocalHom M N a := by
    intro W r s
    obtain ⟨V, rfl⟩ := opensOverPost_surjective f U W
    change Γ(Y, f ''ᵁ V.left) at r
    change Γ(M, f ''ᵁ V.left) at s
    have hb := b.property V ((f.appIso V.left).hom r) s
    rw [← he] at hb
    change a.app (.op ((Over.post f.opensFunctor).obj V))
        ((f.appIso V.left).inv ((f.appIso V.left).hom r) • s) =
      (f.appIso V.left).inv ((f.appIso V.left).hom r) •
        (show Γ(N, f ''ᵁ V.left) from a.app (.op ((Over.post f.opensFunctor).obj V)) s) at hb
    have hr : (f.appIso V.left).inv ((f.appIso V.left).hom r) = r :=
      ConcreteCategory.congr_hom (f.appIso V.left).hom_inv_id r
    erw [hr] at hb
    exact hb
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

def localLinearHomRestrictEquiv (U : X.Opens) :
    Γ(InternalHom.Construction.moduleInternalHom M N, f ''ᵁ U) ≃
      (ModuleHomSheaf.Construction.linearHomSubfunctor (M.restrict f) (N.restrict f)).toFunctor.obj (.op U) :=
  Equiv.ofBijective (localLinearHomRestrict f M N U)
    ⟨localLinearHomRestrict_injective f M N U, localLinearHomRestrict_surjective f M N U⟩

theorem appIso_inv_naturality {U V : X.Opens} (i : V ⟶ U) :
    (f.appIso U).inv ≫ Y.presheaf.map (f.opensFunctor.map i).op =
      X.presheaf.map i.op ≫ (f.appIso V).inv := by
  have he := congrArg (fun z : Γ(Y, f ''ᵁ U) ⟶ Γ(X, V) =>
    (f.appIso U).inv ≫ z ≫ (f.appIso V).inv) (f.appIso_hom_naturality i.op)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at he
  exact he

def moduleInternalHomRestrictHom :
    (InternalHom.Construction.moduleInternalHom M N).restrict f ⟶ InternalHom.Construction.moduleInternalHom (M.restrict f) (N.restrict f) where
  val.app U := ModuleCat.ofHom
    (X := ((InternalHom.Construction.moduleInternalHom M N).restrict f).val.obj U)
    (Y := (InternalHom.Construction.moduleInternalHom (M.restrict f) (N.restrict f)).val.obj U)
    { toFun := localLinearHomRestrict f M N U.unop
      map_add' _ _ := Subtype.ext rfl
      map_smul' r a := by
        apply Subtype.ext
        apply NatTrans.ext
        funext V
        apply AddCommGrpCat.ext
        intro s
        change Y.presheaf.map (f.opensFunctor.map V.unop.hom).op ((f.appIso U.unop).inv r) •
            (show Γ(N, f ''ᵁ V.unop.left) from
              a.val.app (.op ((Over.post f.opensFunctor).obj V.unop)) s) =
          (f.appIso V.unop.left).inv (X.presheaf.map V.unop.hom.op r) •
            (show Γ(N, f ''ᵁ V.unop.left) from
              a.val.app (.op ((Over.post f.opensFunctor).obj V.unop)) s)
        exact congrArg (fun c : Γ(Y, f ''ᵁ V.unop.left) => c •
          (show Γ(N, f ''ᵁ V.unop.left) from
            a.val.app (.op ((Over.post f.opensFunctor).obj V.unop)) s))
          (ConcreteCategory.congr_hom (appIso_inv_naturality f V.unop.hom) r) }
  val.naturality {_U _V} i := by
    ext a
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    apply AddCommGrpCat.ext
    intro s
    rfl

instance moduleInternalHomRestrictHom_isIso : IsIso (moduleInternalHomRestrictHom f M N) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  exact (ConcreteCategory.isIso_iff_bijective ((moduleInternalHomRestrictHom f M N).app U)).mpr
    (localLinearHomRestrictEquiv f M N U).bijective

/-- The internal Hom commutes with restriction to an open subscheme. -/
def moduleInternalHomRestrictIso :
    (InternalHom.Construction.moduleInternalHom M N).restrict f ≅ InternalHom.Construction.moduleInternalHom (M.restrict f) (N.restrict f) :=
  asIso (moduleInternalHomRestrictHom f M N)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHomRestriction
