import OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafTensorPullback

/-! # Free Presheaf Tensor -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FreePresheafTensor

noncomputable section

/-! Tensor products of free local module generators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (X : Scheme.{u})

local instance freePresheafTensorLocal1 : MonoidalCategory X.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory

local instance freePresheafTensorLocal2 (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

local instance freePresheafTensorLocal3 (U : X.Opens) (W : X.Opensᵒᵖ) : Subsingleton ((yoneda.obj U).obj W) :=
  inferInstanceAs (Subsingleton (W.unop ⟶ U))

def productTypePresheaf (F G : X.Opensᵒᵖ ⥤ Type u) : X.Opensᵒᵖ ⥤ Type u where
  obj U := F.obj U × G.obj U
  map f := TypeCat.ofHom (fun p => (F.map f p.1, G.map f p.2))
  map_id U := by ext p <;> simp
  map_comp f g := by ext p <;> simp

def freeModulePresheaf (F : X.Opensᵒᵖ ⥤ Type u) : X.PresheafOfModules :=
  (PresheafOfModules.free X.ringCatSheaf.obj).obj F

theorem freeModulePresheaf_map_freeMk (F : X.Opensᵒᵖ ⥤ Type u)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) (x : F.obj U) :
    (freeModulePresheaf X F).map f (ModuleCat.freeMk x) = ModuleCat.freeMk (F.map f x) :=
  ModuleCat.freeDesc_apply _ x

def freePresheafTensorIso (F G : X.Opensᵒᵖ ⥤ Type u) :
    freeModulePresheaf X F ⊗ freeModulePresheaf X G ≅
      freeModulePresheaf X (productTypePresheaf X F G) :=
  PresheafOfModules.isoMk
    (fun U => ModuleCat.FreeMonoidal.μIso (X.ringCatSheaf.obj.obj U) (F.obj U) (G.obj U)) (by
      intro U V f
      apply (cancel_epi (ModuleCat.FreeMonoidal.μIso
        (X.ringCatSheaf.obj.obj U) (F.obj U) (G.obj U)).inv).mp
      apply ModuleCat.free_hom_ext
      rintro ⟨m, n⟩
      change (ModuleCat.FreeMonoidal.μIso (X.ringCatSheaf.obj.obj V) (F.obj V) (G.obj V)).hom
          ((freeModulePresheaf X F ⊗ freeModulePresheaf X G).map f
            ((ModuleCat.FreeMonoidal.μIso (X.ringCatSheaf.obj.obj U) (F.obj U) (G.obj U)).inv
              (ModuleCat.freeMk (m, n)))) =
        (freeModulePresheaf X (productTypePresheaf X F G)).map f
          ((ModuleCat.FreeMonoidal.μIso (X.ringCatSheaf.obj.obj U) (F.obj U) (G.obj U)).hom
            ((ModuleCat.FreeMonoidal.μIso (X.ringCatSheaf.obj.obj U) (F.obj U) (G.obj U)).inv
              (ModuleCat.freeMk (m, n))))
      erw [ModuleCat.FreeMonoidal.μIso_inv_freeMk,
        PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul,
        freeModulePresheaf_map_freeMk, freeModulePresheaf_map_freeMk,
        ModuleCat.FreeMonoidal.μIso_hom_freeMk_tmul_freeMk,
        ModuleCat.FreeMonoidal.μIso_hom_freeMk_tmul_freeMk, freeModulePresheaf_map_freeMk]
      rfl)

def openYonedaProductIso (U V : X.Opens) :
    productTypePresheaf X (yoneda.obj U) (yoneda.obj V) ≅ yoneda.obj (U ⊓ V) :=
  NatIso.ofComponents (fun W => Equiv.toIso
    { toFun := fun p => homOfLE (le_inf (leOfHom p.1) (leOfHom p.2))
      invFun := fun h => (h ≫ homOfLE inf_le_left, h ≫ homOfLE inf_le_right)
      left_inv := fun _ => Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
      right_inv := fun _ => Subsingleton.elim _ _ }) (by
        intro W Z f
        ext p
        exact Subsingleton.elim _ _)

def freeOpenModulePresheaf (U : X.Opens) : X.PresheafOfModules := freeModulePresheaf X (yoneda.obj U)

def freeOpenTensorIso (U V : X.Opens) :
    freeOpenModulePresheaf X U ⊗ freeOpenModulePresheaf X V ≅ freeOpenModulePresheaf X (U ⊓ V) :=
  freePresheafTensorIso X (yoneda.obj U) (yoneda.obj V) ≪≫
    (PresheafOfModules.free X.ringCatSheaf.obj).mapIso (openYonedaProductIso X U V)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FreePresheafTensor
