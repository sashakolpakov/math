import OAI.AlgebraicGeometry.Comparison.Betti.Module.FrameBases
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Free Sheaf Hom -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FreeSheafHom

noncomputable section

section

/-! The universal property of the actual sheafification of a free module presheaf. -/

open _root_.CategoryTheory

variable {C : Type} [SmallCategory C]

def constantSectionsEquiv (I : Type) (F : Cᵒᵖ ⥤ Type) :
    ((Functor.const Cᵒᵖ).obj I ⟶ F) ≃ (I → F.sections) where
  toFun a i := ⟨fun U => a.app U i, fun f => (NatTrans.naturality_apply a f i).symm⟩
  invFun s :=
    { app := fun U => ↾fun i => (s i).val U
      naturality := fun U V f => by
        ext i
        exact ((s i).property f).symm }
  left_inv a := by ext U i; rfl
  right_inv s := by funext i; apply Subtype.ext; rfl

variable (J : GrothendieckTopology C) (R : Sheaf J RingCat.{0}) (I : Type)

abbrev freePresheaf : PresheafOfModules.{0} R.obj :=
  PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj I)

def sheafifiedFree : SheafOfModules.{0} R :=
  (PresheafOfModules.sheafification.{0} (R := R) (𝟙 R.obj)).obj (freePresheaf J R I)

def sectionsHomEquiv (M : SheafOfModules.{0} R) :
    (sheafifiedFree J R I ⟶ M) ≃ (I → M.sections) :=
  ((PresheafOfModules.sheafificationAdjunction.{0} (R := R) (𝟙 R.obj)).homEquiv
    (freePresheaf J R I) M).trans
      (PresheafOfModules.freeHomEquiv.trans
        (constantSectionsEquiv I (M.val.presheaf ⋙ forget AddCommGrpCat)))

theorem sectionsHomEquiv_naturality {M N : SheafOfModules.{0} R}
    (f : sheafifiedFree J R I ⟶ M) (g : M ⟶ N) (i : I) :
    sectionsHomEquiv J R I N (f ≫ g) i = SheafOfModules.sectionsMap g (sectionsHomEquiv J R I M f i) := by
  apply PresheafOfModules.sections_ext
  intro U
  change (((PresheafOfModules.sheafificationAdjunction.{0} (R := R) (𝟙 R.obj)).homEquiv
      (freePresheaf J R I) N (f ≫ g)).app U) (ModuleCat.freeMk i) =
    g.val.app U ((((PresheafOfModules.sheafificationAdjunction.{0} (R := R) (𝟙 R.obj)).homEquiv
      (freePresheaf J R I) M f).app U) (ModuleCat.freeMk i))
  erw [Adjunction.homEquiv_naturality_right]
  rfl

def homEquiv (M : SheafOfModules.{0} R) :
    (sheafifiedFree J R I ⟶ M) ≃ (SheafOfModules.free (R := R) I ⟶ M) :=
  (sectionsHomEquiv J R I M).trans M.freeHomEquiv.symm

theorem homEquiv_naturality {M N : SheafOfModules.{0} R}
    (f : sheafifiedFree J R I ⟶ M) (g : M ⟶ N) :
    FreeSheafHom.homEquiv J R I N (f ≫ g) = FreeSheafHom.homEquiv J R I M f ≫ g := by
  apply N.freeHomEquiv.injective
  funext i
  change N.freeHomEquiv (N.freeHomEquiv.symm (sectionsHomEquiv J R I N (f ≫ g))) i = _
  rw [Equiv.apply_symm_apply, SheafOfModules.freeHomEquiv_comp_apply]
  change _ = SheafOfModules.sectionsMap g
    (M.freeHomEquiv (M.freeHomEquiv.symm (sectionsHomEquiv J R I M f)) i)
  rw [Equiv.apply_symm_apply]
  exact sectionsHomEquiv_naturality J R I f g i

end

/-! Canonical identification of sheafified free module presheaves with native free module sheaves. -/

open _root_.CategoryTheory

variable {C : Type} [SmallCategory C]
  (J : GrothendieckTopology C) (R : Sheaf J RingCat.{0}) (I : Type)

def sheafifiedFreeIso : sheafifiedFree J R I ≅ SheafOfModules.free (R := R) I where
  hom := (FreeSheafHom.homEquiv J R I (SheafOfModules.free (R := R) I)).symm (𝟙 _)
  inv := FreeSheafHom.homEquiv J R I (sheafifiedFree J R I) (𝟙 _)
  hom_inv_id := by
    apply (FreeSheafHom.homEquiv J R I (sheafifiedFree J R I)).injective
    rw [homEquiv_naturality, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := homEquiv_naturality J R I (𝟙 (sheafifiedFree J R I))
      ((FreeSheafHom.homEquiv J R I (SheafOfModules.free (R := R) I)).symm (𝟙 _))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    exact h.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.FreeSheafHom
