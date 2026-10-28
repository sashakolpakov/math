import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Sheaf Restriction -/

namespace OAI.AlgebraicGeometry.SheafCohomology.SheafRestriction.Projective

noncomputable section

/-! Restriction to an open slice commutes with module sheafification.
This is the local comparison needed for the sheafified tensor powers in ProjectiveCohomology. -/

open _root_.CategoryTheory

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{0}) (U : C)

def overPresheaf : PresheafOfModules.{0} R.obj ⥤
    PresheafOfModules.{0} (R.over U).obj :=
  PresheafOfModules.pushforward (F := Over.forget U) (𝟙 (R.over U).obj)

def overSheafificationMap (M : PresheafOfModules.{0} R.obj) :
    (PresheafOfModules.sheafification (𝟙 (R.over U).obj)).obj
        ((overPresheaf R U).obj M) ⟶
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj M).over U :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (R.over U).obj)).symm
    ((overPresheaf R U).map ((PresheafOfModules.sheafificationAdjunction
      (𝟙 R.obj)).unit.app M))

theorem overSheafificationMap_underlying (M : PresheafOfModules.{0} R.obj) :
    (SheafOfModules.toSheaf (R.over U)).map (overSheafificationMap R U M) =
      ((Over.forget U).pushforwardContinuousSheafificationCompatibility
        AddCommGrpCat (J.over U) J).hom.app M.presheaf := by
  unfold overSheafificationMap
  erw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply ((sheafificationAdjunction (J.over U) AddCommGrpCat).homEquiv _ _).injective
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact ((Over.forget U).toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat (J.over U) J M.presheaf).symm

instance overSheafificationMap_isIso (M : PresheafOfModules.{0} R.obj) :
    IsIso (overSheafificationMap R U M) := by
  have : IsIso ((SheafOfModules.toSheaf (R.over U)).map
      (overSheafificationMap R U M)) := by
    rw [overSheafificationMap_underlying]
    exact ((Over.forget U).pushforwardContinuousSheafificationCompatibility
      AddCommGrpCat (J.over U) J).app M.presheaf |>.isIso_hom
  exact isIso_of_reflects_iso (overSheafificationMap R U M)
    (SheafOfModules.toSheaf (R.over U))

def overSheafificationIso (M : PresheafOfModules.{0} R.obj) :
    (PresheafOfModules.sheafification (𝟙 (R.over U).obj)).obj
        ((overPresheaf R U).obj M) ≅
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj M).over U :=
  asIso (overSheafificationMap R U M)

end

end OAI.AlgebraicGeometry.SheafCohomology.SheafRestriction.Projective
