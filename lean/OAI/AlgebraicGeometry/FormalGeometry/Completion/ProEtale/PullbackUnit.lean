import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackTypes

/-! # Pullback Unit -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackUnit.Construction

noncomputable section

/-!
# Completion: the unit of inverse image in the Kan-extension construction

This records the canonical maps on the construction of inverse image, so
the comparison between abelian sheaves and sheaves of sets can be checked
on the actual integer generator.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type w) [Category.{v} A]
  [HasWeakSheafify (Scheme.ProEt.topology X) A]
  [∀ P : Y.ProEtᵒᵖ ⥤ A, (ProetalePullback.Construction.proEtBaseChange f).op.HasLeftKanExtension P]

/-- The constructed inverse-image unit is the Kan-extension unit followed by sheafification. -/
theorem proEtConstructedPullback_unit (P : Sheaf (Scheme.ProEt.topology Y) A) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (ProetalePullback.Construction.proEtBaseChange f) A
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app P).hom =
      (ProetalePullback.Construction.proEtBaseChange f).op.leftKanExtensionUnit P.obj ≫
        Functor.whiskerLeft (ProetalePullback.Construction.proEtBaseChange f).op
          (toSheafify (Scheme.ProEt.topology X) ((ProetalePullback.Construction.proEtBaseChange f).op.leftKanExtension P.obj)) := by
  change (sheafToPresheaf _ _).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (ProetalePullback.Construction.proEtBaseChange f) A
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app P) = _
  simp only [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app,
    Functor.lanAdjunction_unit, Functor.lanUnit,
    sheafificationAdjunction_unit_app, Iso.refl_hom, NatTrans.id_app,
    Functor.comp_map]
  change (_ ≫ _) ≫ Functor.whiskerLeft (ProetalePullback.Construction.proEtBaseChange f).op (𝟙 _) ≫ 𝟙 _ = _
  simp only [Functor.whiskerLeft_id', Category.comp_id]
  rfl

/-- The abstract-to-constructed comparison preserves the inverse-image unit. -/
theorem proEtPullbackConstructionIso_unit (P : Sheaf (Scheme.ProEt.topology Y) A) :
    ((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous A
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app P ≫
      ((ProetalePullback.Construction.proEtBaseChange f).sheafPushforwardContinuous A
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
        ((Functor.sheafPullbackConstruction.sheafPullbackIso (ProetalePullback.Construction.proEtBaseChange f) A
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).hom.app P) =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (ProetalePullback.Construction.proEtBaseChange f) A
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app P :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ _

/-- The same unit compatibility on underlying presheaves. -/
theorem proEtPullbackConstructionIso_unit_hom (P : Sheaf (Scheme.ProEt.topology Y) A) :
    (((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous A
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app P).hom ≫
      Functor.whiskerLeft (ProetalePullback.Construction.proEtBaseChange f).op
        ((Functor.sheafPullbackConstruction.sheafPullbackIso (ProetalePullback.Construction.proEtBaseChange f) A
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).hom.app P).hom =
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (ProetalePullback.Construction.proEtBaseChange f) A
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app P).hom :=
  congrArg (fun k => k.hom) (proEtPullbackConstructionIso_unit f A P)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackUnit.Construction
