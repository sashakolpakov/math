import OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSheafUniverses
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Integer Sheaf Equivalence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.IntegerSheafEquivalence

noncomputable section

/-! Additive sheaves and sheaves of modules over the lifted integers
are equivalent at the coefficient universe of the actual pro-étale site. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

abbrev coefficients : ModuleCat.{w} (ULift.{w} ℤ) ⥤ AddCommGrpCat.{w} :=
  ModuleCat.restrictScalars (ULift.ringEquiv.symm : ℤ ≃+* ULift.{w} ℤ).toRingHom ⋙
    forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}

variable {C : Type (max u v)} [Category.{v} C] (J : GrothendieckTopology C)

abbrev forgetSheaf : Sheaf J (ModuleCat.{max u v} (ULift.{max u v} ℤ)) ⥤
    Sheaf J AddCommGrpCat.{max u v} := sheafCompose J coefficients

instance forgetSheaf_essSurj : (forgetSheaf J).EssSurj where
  mem_essImage F := by
    let e := coefficients.{max u v}.asEquivalence
    let G := (sheafCompose J e.inverse).obj F
    refine ⟨G, ⟨(fullyFaithfulSheafToPresheaf J AddCommGrpCat.{max u v}).preimageIso ?_⟩⟩
    exact Functor.associator F.obj e.inverse e.functor ≪≫
      Functor.isoWhiskerLeft F.obj e.counitIso ≪≫ Functor.rightUnitor F.obj

instance forgetSheaf_isEquivalence : (forgetSheaf J).IsEquivalence where

instance forgetSheaf_additive : (forgetSheaf J).Additive where
  map_add := by
    intro M N f g
    apply Sheaf.hom_ext
    ext U x
    rfl

abbrev moduleSheaf (H : Sheaf J AddCommGrpCat.{max u v}) :
    Sheaf J (ModuleCat.{max u v} (ULift.{max u v} ℤ)) :=
  (forgetSheaf J).asEquivalence.inverse.obj H

def moduleSheafIso (H : Sheaf J AddCommGrpCat.{max u v}) :
    (forgetSheaf J).obj (moduleSheaf J H) ≅ H :=
  (forgetSheaf J).asEquivalence.counitIso.app H

instance moduleSheaf_injective (H : Sheaf J AddCommGrpCat.{max u v}) [Injective H] :
    Injective (moduleSheaf J H) := by
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.IntegerSheafEquivalence
