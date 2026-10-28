import OAI.AlgebraicGeometry.Comparison.Betti.OverProduct
import OAI.AlgebraicGeometry.Comparison.Betti.OverRingedMorphism

/-! # Over Ringed Composition -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.OverRingedComposition.Modules

noncomputable section

/-! The two actual ring maps for restriction followed by pushforward agree through the product comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  [HasBinaryProducts C] [HasBinaryProducts D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) (U : C)
  [(Over.post (X := U) F).IsContinuous (J.over U) (K.over (F.obj U))]
  [∀ V, IsIso (prodComparison F U V)]

local instance starPost_continuous :
    (Over.star U ⋙ Over.post F).IsContinuous J (K.over (F.obj U)) :=
  Functor.isContinuous_comp _ _ _ (J.over U) _

local instance postStar_continuous :
    (F ⋙ Over.star (F.obj U)).IsContinuous J (K.over (F.obj U)) :=
  Functor.isContinuous_comp _ _ _ K _

def overFirstCompositeStructure : S ⟶
    ((Over.star U ⋙ Over.post F).sheafPushforwardContinuous RingCat J (K.over (F.obj U))).obj
      (R.over (F.obj U)) :=
  SheafOfModules.pushforwardOver (R := S) U ≫
    ((Over.star U).sheafPushforwardContinuous RingCat J (J.over U)).map (OverRingedMorphism.Modules.overStructureMap φ U)

def overSecondCompositeStructure : S ⟶
    ((F ⋙ Over.star (F.obj U)).sheafPushforwardContinuous RingCat J (K.over (F.obj U))).obj
      (R.over (F.obj U)) :=
  φ ≫ (F.sheafPushforwardContinuous RingCat J K).map (SheafOfModules.pushforwardOver (R := R) (F.obj U))

theorem overCompositeStructure_normalization :
    overSecondCompositeStructure φ U ≫
      (Functor.sheafPushforwardContinuousNatTrans (OverProduct.RingedModules.overStarPostIso F U).hom RingCat J
        (K.over (F.obj U))).app (R.over (F.obj U)) = overFirstCompositeStructure φ U := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change (φ.hom.app V ≫ R.obj.map prod.snd.op) ≫ R.obj.map (prodComparison F U V.unop).op =
    S.obj.map prod.snd.op ≫ φ.hom.app (op (U ⨯ V.unop))
  erw [Category.assoc, ← R.obj.map_comp, ← op_comp, prodComparison_snd]
  exact (φ.hom.naturality (prod.snd : U ⨯ V.unop ⟶ V.unop).op).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.OverRingedComposition.Modules
