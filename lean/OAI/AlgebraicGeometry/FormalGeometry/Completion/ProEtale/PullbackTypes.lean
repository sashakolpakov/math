import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Pullback Types -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackTypes.Construction

noncomputable section

/-!
# Completion: inverse image of the underlying sheaves of sets

The filtered Kan-extension formula shows that forgetting the abelian-group
structure commutes with inverse image. This comparison will identify the
torsor of the pulled-back extension with the pullback of its actual scheme.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Inverse image for sheaves of sets in the same universe as the actual torsors. -/
def proEtTypeSheafPullback :
    Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  (ProetalePullback.Construction.proEtBaseChange f).sheafPullback (Type (u + 1))
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

instance proEtTypeLan_preservesFiniteLimits :
    PreservesFiniteLimits ((ProetalePullback.Construction.proEtBaseChange f).op.lan :
      (Y.ProEtᵒᵖ ⥤ Type (u + 1)) ⥤ (X.ProEtᵒᵖ ⥤ Type (u + 1))) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
    ((ProetalePullback.Construction.proEtBaseChange f).op.lan :
      (Y.ProEtᵒᵖ ⥤ Type (u + 1)) ⥤ (X.ProEtᵒᵖ ⥤ Type (u + 1))) J
  intro U
  have : IsFiltered (CostructuredArrow (ProetalePullback.Construction.proEtBaseChange f).op U) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (ProetalePullback.Construction.proEtBaseChange f) U.unop)
  exact preservesLimitsOfShape_of_natIso
    (ProetalePullback.Construction.largeLanEvaluationIsoColim (Type (u + 1)) (ProetalePullback.Construction.proEtBaseChange f).op U).symm

instance proEtTypeSheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits (proEtTypeSheafPullback f) := by
  unfold proEtTypeSheafPullback
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

instance proEtLanForget_preservesPointwise
    (P : Y.ProEtᵒᵖ ⥤ Ab.{u + 1}) (U : X.ProEtᵒᵖ) :
    (forget Ab.{u + 1}).PreservesPointwiseLeftKanExtensionAt P (ProetalePullback.Construction.proEtBaseChange f).op U := by
  have : IsFiltered (CostructuredArrow (ProetalePullback.Construction.proEtBaseChange f).op U) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (ProetalePullback.Construction.proEtBaseChange f) U.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  apply Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit

/-- The Kan extension computing inverse image commutes with forgetting abelian groups. -/
def proEtLanForgetIso :
    (ProetalePullback.Construction.proEtBaseChange f).op.lan ⋙ (Functor.whiskeringRight _ _ _).obj (forget Ab.{u + 1}) ≅
      (Functor.whiskeringRight _ _ _).obj (forget Ab.{u + 1}) ⋙ (ProetalePullback.Construction.proEtBaseChange f).op.lan :=
  (forget Ab.{u + 1}).lanCompIsoOfPreserves (ProetalePullback.Construction.proEtBaseChange f).op

/-- Forgetting abelian groups commutes with the constructed inverse image. -/
def proEtConstructedPullbackForgetIso :
    Functor.sheafPullbackConstruction.sheafPullback (ProetalePullback.Construction.proEtBaseChange f) Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) ⋙
      sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1}) ≅
    sheafCompose (Scheme.ProEt.topology Y) (forget Ab.{u + 1}) ⋙
      Functor.sheafPullbackConstruction.sheafPullback (ProetalePullback.Construction.proEtBaseChange f) (Type (u + 1))
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
  isoWhiskerLeft (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1} ⋙
      (ProetalePullback.Construction.proEtBaseChange f).op.lan)
      (sheafComposeNatIso (Scheme.ProEt.topology X) (forget Ab.{u + 1})
        (sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1})
        (sheafificationAdjunction (Scheme.ProEt.topology X) (Type (u + 1)))).symm ≪≫
    isoWhiskerRight (isoWhiskerLeft (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (proEtLanForgetIso f)) (presheafToSheaf (Scheme.ProEt.topology X) (Type (u + 1)))

/-- The underlying sheaf of the actual abelian inverse image is the inverse image of the
underlying sheaf. -/
def proEtPullbackForgetIso :
    ProetalePullback.Construction.proEtSheafPullback f ⋙ sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y) (forget Ab.{u + 1}) ⋙ proEtTypeSheafPullback f :=
  isoWhiskerRight
      (Functor.sheafPullbackConstruction.sheafPullbackIso (ProetalePullback.Construction.proEtBaseChange f) Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)) _ ≪≫
    proEtConstructedPullbackForgetIso f ≪≫
    isoWhiskerLeft (sheafCompose (Scheme.ProEt.topology Y) (forget Ab.{u + 1}))
      (Functor.sheafPullbackConstruction.sheafPullbackIso (ProetalePullback.Construction.proEtBaseChange f) (Type (u + 1))
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackTypes.Construction
