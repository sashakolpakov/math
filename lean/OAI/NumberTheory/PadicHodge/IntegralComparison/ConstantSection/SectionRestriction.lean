import OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.SheafRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.Coordinates

/-! # Section Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.SectionRestriction

noncomputable section

/-! Constant-module section maps commute with actual presheaf restriction. -/

open _root_.CategoryTheory

universe u v u' v' w z

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [F.IsCocontinuous J K]
  [HasSheafify J (ModuleCat.{w} R)] [HasSheafify K (ModuleCat.{w} R)]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} R, F.op.HasPointwiseRightKanExtension P]
  (M : ModuleCat.{w} R) (N : Sheaf K (ModuleCat.{w} R))
  (a : (constantSheaf K (ModuleCat.{w} R)).obj M ⟶ N)

def constantIso : (F.sheafPushforwardContinuous (ModuleCat.{w} R) J K).obj
    ((constantSheaf K (ModuleCat.{w} R)).obj M) ≅ (constantSheaf J (ModuleCat.{w} R)).obj M :=
  (Constant.SheafRestriction.compatibility F J K (ModuleCat.{w} R) M).symm

def pulled : (constantSheaf J (ModuleCat.{w} R)).obj M ⟶
    (F.sheafPushforwardContinuous (ModuleCat.{w} R) J K).obj N :=
  (constantIso F R J K M).inv ≫ (F.sheafPushforwardContinuous (ModuleCat.{w} R) J K).map a

theorem adjunction : (sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _ (pulled F R J K M N a) =
    Functor.whiskerLeft F.op ((sheafificationAdjunction K (ModuleCat.{w} R)).homEquiv _ _ a) := by
  have h := Constant.SheafRestriction.targetEquiv_map F J K (ModuleCat.{w} R) M N a
  change (sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _
    ((constantIso F R J K M).inv ≫ (F.sheafPushforwardContinuous (ModuleCat.{w} R) J K).map a ≫ 𝟙 _) = _ at h
  rw [Category.comp_id] at h
  exact h

variable [HasExt.{max u w z} (Sheaf J (ModuleCat.{w} R))]
  [HasExt.{max u' w z} (Sheaf K (ModuleCat.{w} R))]

theorem coordinates (m : M) (U : Cᵒᵖ) (r : R) :
    (Ext.ZeroPresheafSections.equivalence R J _
      (Module.ConstantSections.sectionMap R J M _ (pulled F R J K M N a) m)).down.app U r =
    (Ext.ZeroPresheafSections.equivalence R K N
      (Module.ConstantSections.sectionMap R K M N a m)).down.app (F.op.obj U) r := by
  rw [Coordinates.section_apply, Coordinates.section_apply]
  exact congrArg (fun b => b.app U (r • m)) (adjunction F R J K M N a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.SectionRestriction
