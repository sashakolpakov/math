import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback

/-! # Pullback Existence -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackExistence.RingedModules

/-! Actual pullback of module sheaves exists on the small sites used for analytification and its open slices. -/

open _root_.CategoryTheory

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}}
  [HasWeakSheafify K AddCommGrpCat.{0}] [K.WEqualsLocallyBijective AddCommGrpCat.{0}]

theorem smallModulePushforward_isRightAdjoint
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) :
    (SheafOfModules.pushforward.{0} φ).IsRightAdjoint := by
  let : (PresheafOfModules.pushforward.{0} φ.hom).IsRightAdjoint := by
    apply Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    exact PresheafOfModules.pullbackObjIsDefined_eq_top φ.hom
  exact (SheafOfModules.PullbackConstruction.adjunction φ).isRightAdjoint

end OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackExistence.RingedModules
