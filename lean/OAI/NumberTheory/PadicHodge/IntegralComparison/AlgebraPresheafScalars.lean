import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Algebra Presheaf Scalars -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraPresheafScalars

noncomputable section

/-!
# IntegralComparison: restriction from coordinate-module presheaves to their actual base-ring scalars
-/

open _root_.CategoryTheory

universe u v w z

variable (k : Type u) [CommRing k] {C : Type v} [Category.{w} C]
  (H : Cᵒᵖ ⥤ CommAlgCat.{u} k)

abbrev rings : Cᵒᵖ ⥤ RingCat.{u} :=
  H ⋙ forget₂ (CommAlgCat.{u} k) CommRingCat ⋙ forget₂ CommRingCat RingCat

def obj (M : PresheafOfModules.{z} (rings k H)) : Cᵒᵖ ⥤ ModuleCat.{z} k where
  obj U := (ModuleCat.restrictScalars (algebraMap k (H.obj U))).obj (M.obj U)
  map {U V} f := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (algebraMap k (H.obj U))).obj (M.obj U))
    (Y := (ModuleCat.restrictScalars (algebraMap k (H.obj V))).obj (M.obj V))
    { toFun := fun x => M.map f x
      map_add' := (M.map f).hom.map_add
      map_smul' := by
        intro r x
        exact (M.map_smul f (algebraMap k (H.obj U) r) x).trans
          (congrArg (fun a : H.obj V => a • (show M.obj V from M.map f x)) ((H.map f).hom.commutes r)) }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M.map (𝟙 U) x = x
    rw [M.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact M.map_comp_apply f g x

def map {M N : PresheafOfModules.{z} (rings k H)} (φ : M ⟶ N) : AlgebraPresheafScalars.obj k H M ⟶ AlgebraPresheafScalars.obj k H N where
  app U := (ModuleCat.restrictScalars (algebraMap k (H.obj U))).map (φ.app U)
  naturality _ _ f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact PresheafOfModules.naturality_apply φ f x

def functor : PresheafOfModules.{z} (rings k H) ⥤ (Cᵒᵖ ⥤ ModuleCat.{z} k) where
  obj := AlgebraPresheafScalars.obj k H
  map := AlgebraPresheafScalars.map k H

instance additive : (functor k H).Additive where
  map_add := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraPresheafScalars
