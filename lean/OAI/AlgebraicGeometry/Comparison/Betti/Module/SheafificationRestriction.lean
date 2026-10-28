import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Sheafification Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafificationRestriction

noncomputable section

/-! Sheafification of modules commutes with restriction along a continuous, cocontinuous site functor. -/

open _root_.CategoryTheory

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{0}] [HasSheafify K AddCommGrpCat.{0}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {F : C ⥤ D} [F.IsContinuous J K] [F.IsCocontinuous J K]
  {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{0} J K).obj R)
  (P : PresheafOfModules.{0} R.obj)

def sheafificationRestrictionMap :
    (PresheafOfModules.sheafification.{0} (R := S) (𝟙 S.obj)).obj
      ((PresheafOfModules.pushforward φ.hom).obj P) ⟶
    (SheafOfModules.pushforward φ).obj
      ((PresheafOfModules.sheafification.{0} (R := R) (𝟙 R.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj)).symm
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (R := R) (𝟙 R.obj)).unit.app P))

theorem sheafificationRestrictionMap_isIso : IsIso (sheafificationRestrictionMap φ P) := by
  suffices h : IsIso ((SheafOfModules.toSheaf.{0} S).map
      (sheafificationRestrictionMap φ P)) by
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf.{0} S)
  unfold sheafificationRestrictionMap
  erw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  let Q : Sheaf J AddCommGrpCat.{0} :=
    (F.sheafPushforwardContinuous AddCommGrpCat.{0} J K).obj
      ((presheafToSheaf K AddCommGrpCat.{0}).obj P.presheaf)
  let g : F.op ⋙ P.presheaf ⟶ (sheafToPresheaf J AddCommGrpCat.{0}).obj Q :=
    Functor.whiskerLeft F.op (toSheafify K P.presheaf)
  have : Presheaf.IsLocallyInjective J g :=
    Presheaf.isLocallyInjective_whisker J K F (toSheafify K P.presheaf)
  have : Presheaf.IsLocallySurjective J g :=
    Presheaf.isLocallySurjective_whisker J K F (toSheafify K P.presheaf)
  have : IsIso ((presheafToSheaf J AddCommGrpCat.{0}).map g) :=
    (J.W_iff g).mp (J.W_of_isLocallyBijective g)
  change IsIso (((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{0}).homEquiv
    (F.op ⋙ P.presheaf) Q).symm g)
  rw [Adjunction.homEquiv_counit]
  infer_instance

def sheafificationRestrictionIso :
    (PresheafOfModules.sheafification.{0} (R := S) (𝟙 S.obj)).obj
      ((PresheafOfModules.pushforward φ.hom).obj P) ≅
    (SheafOfModules.pushforward φ).obj
      ((PresheafOfModules.sheafification.{0} (R := R) (𝟙 R.obj)).obj P) := by
  have : IsIso (sheafificationRestrictionMap φ P) := sheafificationRestrictionMap_isIso φ P
  exact asIso (sheafificationRestrictionMap φ P)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafificationRestriction
