import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Constant Subpresheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.ConstantSubpresheaf

noncomputable section

/-!
# IntegralComparison: the constant presheaf extended by zero from an incoming-closed full subcategory
-/

open _root_.CategoryTheory Opposite

universe u v w

variable {C : Type u} [Category.{v} C] (R : Type w) [Ring R] (M : ModuleCat.{w} R)
  (P : ObjectProperty C) (hP : ∀ {U V : C}, (U ⟶ V) → P V → P U)

def support (U : C) : Submodule R M := by
  classical
  exact if P U then ⊤ else ⊥

include hP in
theorem support_mono {U V : C} (α : U ⟶ V) : support R M P V ≤ support R M P U := by
  classical
  by_cases h : P V
  · simp only [support, ite_eq_left h, ite_eq_left (hP α h), le_refl]
  · simp only [support, ite_eq_right h, bot_le]

def presheaf : Cᵒᵖ ⥤ ModuleCat.{w} R where
  obj U := ModuleCat.of R (support R M P U.unop)
  map α := ModuleCat.ofHom (Submodule.inclusion (support_mono R M P hP α.unop))
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

def inclusion : presheaf R M P hP ⟶ (Functor.const Cᵒᵖ).obj M where
  app U := ModuleCat.ofHom (support R M P U.unop).subtype
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext (fun _ => rfl))

instance inclusion_app_mono (U : Cᵒᵖ) : Mono ((ConstantSubpresheaf.inclusion R M P hP).app U) :=
  (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

instance inclusion_mono : Mono (ConstantSubpresheaf.inclusion R M P hP) := NatTrans.mono_of_mono_app _

theorem support_eq_zero {U : C} (hU : ¬ P U) (x : support R M P U) : x = 0 := by
  apply Subtype.ext
  change (x.val : M) = (0 : M)
  have h := x.property
  simpa only [support, ite_eq_right hU, Submodule.mem_bot] using h

variable (F : Cᵒᵖ ⥤ ModuleCat.{w} R)
  (a : (Functor.const P.FullSubcategoryᵒᵖ).obj M ⟶ P.ι.op ⋙ F)

def liftMap (U : C) : support R M P U →ₗ[R] F.obj (op U) := by
  classical
  exact if h : P U then ((a.app (op ⟨U, h⟩)).hom.comp (support R M P U).subtype) else 0

theorem liftMap_inside (U : C) (hU : P U) (x : support R M P U) :
    liftMap R M P F a U x = a.app (op ⟨U, hU⟩) x.val := by
  simp only [liftMap, dite_eq_left hU, LinearMap.comp_apply, Submodule.subtype_apply]

def lift : presheaf R M P hP ⟶ F where
  app U := ModuleCat.ofHom (liftMap R M P F a U.unop)
  naturality U V α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    classical
    by_cases hU : P U.unop
    · have hV := hP α.unop hU
      have h := congrArg (fun g : M ⟶ F.obj V => g x.val)
        (a.naturality (ObjectProperty.homMk α.unop :
          (⟨V.unop, hV⟩ : P.FullSubcategory) ⟶ ⟨U.unop, hU⟩).op)
      exact (liftMap_inside R M P F a V.unop hV _).trans
        (h.trans (congrArg (F.map α) (liftMap_inside R M P F a U.unop hU x)).symm)
    · have hx := support_eq_zero R M P hU x
      subst x
      exact (map_zero _).trans ((congrArg (F.map α) (map_zero _)).trans (map_zero _)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.ConstantSubpresheaf
