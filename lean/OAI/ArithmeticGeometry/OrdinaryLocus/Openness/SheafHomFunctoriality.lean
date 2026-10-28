import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation

/-! # Sheaf Hom Functoriality -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction

noncomputable section

/-! Functoriality of the sheaf of module homomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def localModuleHomMap {X : Scheme.{u}} {M M' N N' : X.Modules}
    (a : M' ⟶ M) (b : N ⟶ N') (U : X.Opens)
    (q : ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M N U) : ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M' N' U :=
  ModuleHomSheaf.Construction.moduleHomFromOver M' N' U (a.over U ≫ ModuleHomSheaf.Construction.moduleHomToOver M N U q ≫ b.over U)

theorem localModuleHomMap_apply {X : Scheme.{u}} {M M' N N' : X.Modules}
    (a : M' ⟶ M) (b : N ⟶ N') (U : X.Opens)
    (q : ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M N U) (V : Over U) (m : Γ(M', V.left)) :
    (localModuleHomMap a b U q).1.app (.op V) m =
      b.app V.left (q.1.app (.op V) (a.app V.left m)) := rfl

def sheafHomMapAtOpen {X : Scheme.{u}} {M M' N N' : X.Modules}
    (a : M' ⟶ M) (b : N ⟶ N') (U : X.Opens) :
    (SheafHomModule.Construction.sheafHomModule M N).val.obj (.op U) →ₗ[X.ringCatSheaf.obj.obj (.op U)]
      (SheafHomModule.Construction.sheafHomModule M' N').val.obj (.op U) where
  toFun := localModuleHomMap a b U
  map_add' q q' := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    exact (b.app V.unop.left).hom.map_add _ _
  map_smul' r q := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    exact Scheme.Modules.Hom.app_smul b (X.presheaf.map V.unop.hom.op r)
      (q.1.app V (a.app V.unop.left m))

def sheafHomMap {X : Scheme.{u}} {M M' N N' : X.Modules}
    (a : M' ⟶ M) (b : N ⟶ N') : SheafHomModule.Construction.sheafHomModule M N ⟶ SheafHomModule.Construction.sheafHomModule M' N' where
  val :=
    { app U := ModuleCat.ofHom (R := X.ringCatSheaf.obj.obj U)
        (X := (SheafHomModule.Construction.sheafHomModule M N).val.obj U) (Y := (SheafHomModule.Construction.sheafHomModule M' N').val.obj U)
        (sheafHomMapAtOpen a b U.unop)
      naturality {U V} h := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro q
        apply Subtype.ext
        apply NatTrans.ext
        funext W
        ext m
        rfl }

theorem sheafHomMap_id {X : Scheme.{u}} (M N : X.Modules) :
    sheafHomMap (𝟙 M) (𝟙 N) = 𝟙 (SheafHomModule.Construction.sheafHomModule M N) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  ext m
  rfl

theorem sheafHomMap_comp {X : Scheme.{u}} {M M' M'' N N' N'' : X.Modules}
    (a : M' ⟶ M) (a' : M'' ⟶ M') (b : N ⟶ N') (b' : N' ⟶ N'') :
    sheafHomMap (a' ≫ a) (b ≫ b') = sheafHomMap a b ≫ sheafHomMap a' b' := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  ext m
  rfl

def sheafHomCongr {X : Scheme.{u}} {M M' N N' : X.Modules}
    (a : M ≅ M') (b : N ≅ N') : SheafHomModule.Construction.sheafHomModule M N ≅ SheafHomModule.Construction.sheafHomModule M' N' where
  hom := sheafHomMap a.inv b.hom
  inv := sheafHomMap a.hom b.inv
  hom_inv_id := by rw [← sheafHomMap_comp, a.hom_inv_id, b.hom_inv_id, sheafHomMap_id]
  inv_hom_id := by rw [← sheafHomMap_comp, a.inv_hom_id, b.inv_hom_id, sheafHomMap_id]

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction
