import OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackOver
import OAI.AlgebraicGeometry.Comparison.Betti.OverPost
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Pullback Local Frames -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackLocalFrames.RingedModules

noncomputable section

/-! Actual local free module frames pull back to free frames on the corresponding open slice. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  [HasBinaryProducts C] [HasBinaryProducts D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) (U : C)
  [(Over.post (X := U) F).IsContinuous (J.over U) (K.over (F.obj U))]
  [∀ V, IsIso (prodComparison F U V)]
  [(SheafOfModules.pushforward.{0} φ).IsRightAdjoint]
  [(SheafOfModules.pushforward.{0} (OverRingedMorphism.Modules.overStructureMap φ U)).IsRightAdjoint]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{0}]
  [HasWeakSheafify (K.over (F.obj U)) AddCommGrpCat.{0}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [(K.over (F.obj U)).WEqualsLocallyBijective AddCommGrpCat.{0}]

def modulePullbackOverFreeIso (M : SheafOfModules.{0} S) (I : Type)
    (e : SheafOfModules.free (R := S.over U) I ≅ M.over U) :
    SheafOfModules.free (R := R.over (F.obj U)) I ≅
      ((SheafOfModules.pullback φ).obj M).over (F.obj U) := by
  let : (Over.post (X := U) F).Final := OverPost.RingedModules.overPost_final F U
  exact (SheafOfModules.pullbackObjFreeIso (OverRingedMorphism.Modules.overStructureMap φ U) I).symm ≪≫
    (SheafOfModules.pullback (OverRingedMorphism.Modules.overStructureMap φ U)).mapIso e ≪≫
      ((PullbackOver.RingedModules.modulePullbackOverIso φ U).app M).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackLocalFrames.RingedModules
