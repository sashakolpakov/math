import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Picard
import OAI.AlgebraicGeometry.FormalGeometry.Completion.StructureSheafBaseChange
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackCompositionMap

/-! # Flat Picard Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatPicardDescent.Construction

noncomputable section

/-! Actual Picard pullback is injective for structure-preserving proper maps
and for their flat base changes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {X Y Z S : Scheme.{u}}

theorem picardPullback_injective_of_app_isIso (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) :
    Function.Injective (Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map f) := by
  have hi : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact (ConcreteCategory.isIso_iff_bijective (f.app U)).mp (hf U)
  exact Quotients.FiniteDescent.Picard.Construction.PicardDescent.injective f
    (@asIso _ _ _ _ (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) hi)

theorem proper_flat_isPullback_picard_injective (c : Z ⟶ X) [IsProper c]
    (f : Y ⟶ X) [Flat f]
    (hc : ∀ U : X.Opens, IsAffineOpen U → IsIso (c.app U))
    {W : Scheme.{u}} {p : W ⟶ Z} {q : W ⟶ Y} (H : IsPullback p q c f) :
    Function.Injective (Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map q) :=
  picardPullback_injective_of_app_isIso q (StructureSheafBaseChange.Construction.proper_flat_isPullback_app_isIso c f hc H)

theorem pullbackCompositionMap_app_isIso (f : X ⟶ S) (c : Z ⟶ X) [IsProper c]
    (g : Y ⟶ S) [Flat g] (hc : ∀ U : X.Opens, IsIso (c.app U))
    (V : (pullback f g).Opens) : IsIso ((PullbackCompositionMap.Construction.pullbackCompositionMap f c g).app V) :=
  StructureSheafBaseChange.Construction.proper_flat_isPullback_app_isIso c (pullback.fst f g) (fun U _ => hc U)
    (PullbackCompositionMap.Construction.pullbackCompositionMap_isPullback f c g).flip V

theorem pullbackCompositionMap_picard_injective (f : X ⟶ S) (c : Z ⟶ X) [IsProper c]
    (g : Y ⟶ S) [Flat g] (hc : ∀ U : X.Opens, IsIso (c.app U)) :
    Function.Injective (Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (PullbackCompositionMap.Construction.pullbackCompositionMap f c g)) :=
  picardPullback_injective_of_app_isIso _ (pullbackCompositionMap_app_isIso f c g hc)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatPicardDescent.Construction
