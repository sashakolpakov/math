import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-! # Open Kan Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.OpenKanEvaluation.LargeOpenKanEvaluation

noncomputable section

/-! # Pointwise left Kan evaluation in the larger coefficient-module universe -/

open _root_.CategoryTheory Limits

universe u

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  (R : Type (u + 1)) [CommRing R]

local instance moduleColimits : HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasColimitsOfSize.{u + 1, u + 1, u, u} R

def iso (F : C ⥤ D) (X : D) :
    F.lan ⋙ (evaluation D (ModuleCat.{u + 1} R)).obj X ≅
      (Functor.whiskeringLeft _ _ (ModuleCat.{u + 1} R)).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G => F.leftKanExtensionObjIsoColimit G X) (fun {G₁ G₂} φ => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
    intro T
    let η : F.leftKanExtension G₁ ⟶ F.leftKanExtension G₂ := F.lan.map φ
    have h₁ := fun (G : C ⥤ ModuleCat.{u + 1} R) => F.ι_leftKanExtensionObjIsoColimit_hom G X T
    have h₂ : φ.app T.left ≫ (F.leftKanExtensionUnit G₂).app T.left =
        (F.leftKanExtensionUnit G₁).app T.left ≫ η.app (F.obj T.left) :=
      congr_app (F.lanUnit.naturality φ) T.left
    change ((F.leftKanExtensionUnit G₁).app T.left ≫ (F.leftKanExtension G₁).map T.hom) ≫
        (η.app X ≫ (F.leftKanExtensionObjIsoColimit G₂ X).hom) =
      ((F.leftKanExtensionUnit G₁).app T.left ≫ (F.leftKanExtension G₁).map T.hom) ≫
        ((F.leftKanExtensionObjIsoColimit G₁ X).hom ≫
          colimMap (Functor.whiskerLeft (CostructuredArrow.proj F X) φ))
    simp only [Category.assoc]
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁]
    exact (ι_colimMap (Functor.whiskerLeft (CostructuredArrow.proj F X) φ) T).symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.OpenKanEvaluation.LargeOpenKanEvaluation
