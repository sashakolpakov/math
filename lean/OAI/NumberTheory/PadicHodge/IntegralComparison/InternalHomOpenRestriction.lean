import OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeInternalHom
import OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHomRestriction

/-! # Internal Hom Open Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomOpenRestriction

noncomputable section

/-! Restriction preserves the actual internal Hom used by the dual
resolution, including its module structure and its source maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  (M N : Y.Modules)

def localHom (U : X.Opens) (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, f ''ᵁ U)) :
    Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (M.restrict f) (N.restrict f), U) :=
  ⟨Functor.whiskerLeft (Over.post f.opensFunctor).op q.val, by
    intro V r
    ext s
    exact ConcreteCategory.congr_hom
      (q.property ((Over.post f.opensFunctor).obj V) ((f.appIso V.left).inv r)) s⟩

theorem localHom_injective (U : X.Opens) : Function.Injective (localHom f M N U) := by
  intro a b h
  apply Subtype.ext
  let F := (Functor.whiskeringLeft (Over U)ᵒᵖ (Over (f ''ᵁ U))ᵒᵖ AddCommGrpCat).obj
    (Over.post f.opensFunctor).op
  exact F.map_injective (congrArg Subtype.val h)

theorem localHom_surjective (U : X.Opens) : Function.Surjective (localHom f M N U) := by
  intro b
  let F := (Functor.whiskeringLeft (Over U)ᵒᵖ (Over (f ''ᵁ U))ᵒᵖ AddCommGrpCat).obj
    (Over.post f.opensFunctor).op
  let a : (presheafHom M.presheaf N.presheaf).obj (op (f ''ᵁ U)) := F.preimage b.val
  have he : Functor.whiskerLeft (Over.post f.opensFunctor).op a = b.val :=
    F.map_preimage (X := (Over.forget (f ''ᵁ U)).op ⋙ M.presheaf)
      (Y := (Over.forget (f ''ᵁ U)).op ⋙ N.presheaf) b.val
  have ha : a ∈ (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomSubfunctor M N).obj (op (f ''ᵁ U)) := by
    intro W r
    obtain ⟨V, rfl⟩ := AlgebraicGeometry.Picard.Homomorphisms.InternalHomRestriction.Construction.opensOverPost_surjective f U W
    change Γ(Y, f ''ᵁ V.left) at r
    ext s
    change Γ(M, f ''ᵁ V.left) at s
    have hb := ConcreteCategory.congr_hom
      (b.property V ((f.appIso V.left).hom r)) s
    rw [← he] at hb
    change a.app (op ((Over.post f.opensFunctor).obj V))
        ((f.appIso V.left).inv ((f.appIso V.left).hom r) • s) =
      (f.appIso V.left).inv ((f.appIso V.left).hom r) •
        (show Γ(N, f ''ᵁ V.left) from
          a.app (op ((Over.post f.opensFunctor).obj V)) s) at hb
    have hr : (f.appIso V.left).inv ((f.appIso V.left).hom r) = r :=
      ConcreteCategory.congr_hom (f.appIso V.left).hom_inv_id r
    rw [hr] at hb
    exact hb
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

def hom : (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N).restrict f ⟶
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (M.restrict f) (N.restrict f) where
  val.app U := ModuleCat.ofHom
    (X := ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N).restrict f).val.obj U)
    (Y := (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (M.restrict f) (N.restrict f)).val.obj U)
    { toFun := localHom f M N U.unop
      map_add' _ _ := Subtype.ext rfl
      map_smul' r a := by
        apply Subtype.ext
        apply NatTrans.ext
        funext V
        apply AddCommGrpCat.ext
        intro s
        change Y.presheaf.map (f.opensFunctor.map V.unop.hom).op ((f.appIso U.unop).inv r) •
            (show Γ(N, f ''ᵁ V.unop.left) from
              a.val.app (op ((Over.post f.opensFunctor).obj V.unop)) s) =
          (f.appIso V.unop.left).inv (X.presheaf.map V.unop.hom.op r) •
            (show Γ(N, f ''ᵁ V.unop.left) from
              a.val.app (op ((Over.post f.opensFunctor).obj V.unop)) s)
        exact congrArg (fun c : Γ(Y, f ''ᵁ V.unop.left) => c •
          (show Γ(N, f ''ᵁ V.unop.left) from
            a.val.app (op ((Over.post f.opensFunctor).obj V.unop)) s))
          (ConcreteCategory.congr_hom (AlgebraicGeometry.Picard.Homomorphisms.InternalHomRestriction.Construction.appIso_inv_naturality f V.unop.hom) r) }
  val.naturality {_U _V} i := by
    ext a
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    apply AddCommGrpCat.ext
    intro s
    rfl

instance hom_isIso : IsIso (InternalHomOpenRestriction.hom f M N) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  exact (ConcreteCategory.isIso_iff_bijective ((InternalHomOpenRestriction.hom f M N).app U)).mpr
    ⟨localHom_injective f M N U, localHom_surjective f M N U⟩

def iso : (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N).restrict f ≅
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (M.restrict f) (N.restrict f) :=
  asIso (InternalHomOpenRestriction.hom f M N)

theorem precomp {M' : Y.Modules} (a : M ⟶ M') :
    (Scheme.Modules.restrictFunctor f).map (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap a (𝟙 N)) ≫
        (iso f M N).hom =
      (iso f M' N).hom ≫ ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap
        ((Scheme.Modules.restrictFunctor f).map a) (𝟙 (N.restrict f)) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext q
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  ext s
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomOpenRestriction
