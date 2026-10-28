import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Over Ringed Morphism -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.OverRingedMorphism.Modules

noncomputable section

/-! Restrict an actual morphism of ringed sites to the corresponding slice sites. -/

open _root_.CategoryTheory Opposite

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {S : Sheaf J RingCat.{0}} {R : Sheaf K RingCat.{0}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) (U : C)
  [(Over.post (X := U) F).IsContinuous (J.over U) (K.over (F.obj U))]

def overStructureMap : S.over U ⟶
    ((Over.post (X := U) F).sheafPushforwardContinuous RingCat (J.over U) (K.over (F.obj U))).obj
      (R.over (F.obj U)) where
  hom :=
    { app V := φ.hom.app (op V.unop.left)
      naturality := by
        intro V W f
        exact φ.hom.naturality ((Over.forget U).map f.unop).op }

theorem overStructureMap_apply (V : (Over U)ᵒᵖ) (s : S.obj.obj (op V.unop.left)) :
    (overStructureMap φ U).hom.app V s = φ.hom.app (op V.unop.left) s := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.OverRingedMorphism.Modules
