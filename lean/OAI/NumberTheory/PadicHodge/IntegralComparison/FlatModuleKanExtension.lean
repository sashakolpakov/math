import Mathlib

/-! # Flat Module Kan Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FlatModuleKanExtension

noncomputable section

/-!
# IntegralComparison: exact module-valued left Kan extension with separate site universes

The sites have an object universe larger than their morphism universe.
The pointwise colimit formula and exactness of filtered module colimits
prove finite-limit preservation at those actual universes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (R : Type (max u v)) [Ring R]

def evaluationIso (F : C ⥤ D) (X : D) :
    F.lan ⋙ (evaluation D (ModuleCat.{max u v} R)).obj X ≅
      (Functor.whiskeringLeft _ _ (ModuleCat.{max u v} R)).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G => F.leftKanExtensionObjIsoColimit G X) (fun {G₁ G₂} φ => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
    intro T
    let η : F.leftKanExtension G₁ ⟶ F.leftKanExtension G₂ := F.lan.map φ
    have h₁ := fun (G : C ⥤ ModuleCat.{max u v} R) =>
      F.ι_leftKanExtensionObjIsoColimit_hom G X T
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

lemma preservesFiniteLimits (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ Dᵒᵖ ⥤ ModuleCat.{max u v} R) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{max u v}
  intro K _ _
  apply preservesLimitsOfShape_of_evaluation
    (F.op.lan : (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ Dᵒᵖ ⥤ ModuleCat.{max u v} R) K
  intro X
  have : IsFiltered (CostructuredArrow F.op X) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop X))
  have : AB5OfSize.{v, max u v} (ModuleCat.{max u v} R) :=
    AB5OfSize_of_univLE (ModuleCat.{max u v} R)
  exact preservesLimitsOfShape_of_natIso (evaluationIso R F.op X).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FlatModuleKanExtension
