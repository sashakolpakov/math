import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Sheafification Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafificationRestriction

noncomputable section

/-!
# IntegralComparison: module sheafification commutes with continuous and cocontinuous geometric restriction
-/

open _root_.CategoryTheory

universe u

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C ⥤ D} [F.IsContinuous J K] [F.IsCocontinuous J K]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (P : PresheafOfModules.{u} R.obj)

def map :
    (PresheafOfModules.sheafification (R := S) (𝟙 S.obj)).obj
      ((PresheafOfModules.pushforward φ.hom).obj P) ⟶
    (SheafOfModules.pushforward φ).obj ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj)).symm
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)).unit.app P))

theorem map_isIso : IsIso (SheafificationRestriction.map φ P) := by
  suffices h : IsIso ((SheafOfModules.toSheaf.{u} S).map (SheafificationRestriction.map φ P)) by
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf.{u} S)
  unfold SheafificationRestriction.map
  erw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  let Q : Sheaf J AddCommGrpCat.{u} :=
    (F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj
      ((presheafToSheaf K AddCommGrpCat.{u}).obj P.presheaf)
  let g : F.op ⋙ P.presheaf ⟶ (sheafToPresheaf J AddCommGrpCat.{u}).obj Q :=
    Functor.whiskerLeft F.op (toSheafify K P.presheaf)
  let : Presheaf.IsLocallyInjective J g :=
    Presheaf.isLocallyInjective_whisker J K F (toSheafify K P.presheaf)
  let : Presheaf.IsLocallySurjective J g :=
    Presheaf.isLocallySurjective_whisker J K F (toSheafify K P.presheaf)
  let : IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map g) :=
    (J.W_iff g).mp (J.W_of_isLocallyBijective g)
  change IsIso (((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
    (F.op ⋙ P.presheaf) Q).symm g)
  rw [Adjunction.homEquiv_counit]
  infer_instance

def iso :
    (PresheafOfModules.sheafification (R := S) (𝟙 S.obj)).obj
      ((PresheafOfModules.pushforward φ.hom).obj P) ≅
    (SheafOfModules.pushforward φ).obj ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P) := by
  let : IsIso (SheafificationRestriction.map φ P) := map_isIso φ P
  exact asIso (SheafificationRestriction.map φ P)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafificationRestriction
