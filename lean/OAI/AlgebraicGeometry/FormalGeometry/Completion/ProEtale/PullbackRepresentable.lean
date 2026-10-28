import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackTypes
import Mathlib.CategoryTheory.Sites.Subcanonical

/-! # Pullback Representable -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackRepresentable.Construction

noncomputable section

/-!
# Completion: inverse image carries actual represented sheaves to base-changed schemes

The sheaf adjunction and Yoneda lemma identify the two corepresentations
of evaluation at the base-changed site object. This proves the comparison
on the whole site.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.ProEt)

/-- Yoneda and the inverse-image adjunction give the first corepresentation of evaluation. -/
def proEtPullbackEvaluationCorepresentative :
    ((sheafSections (Scheme.ProEt.topology X) (Type (u + 1))).obj
      (op ((ProetalePullback.Construction.proEtBaseChange f).obj U))).CorepresentableBy
        ((PullbackTypes.Construction.proEtTypeSheafPullback f).obj ((Scheme.ProEt.topology Y).uliftYoneda.{u + 1}.obj U)) where
  homEquiv {F} :=
    (((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).homEquiv _ F).trans
        (Scheme.ProEt.topology Y).uliftYonedaEquiv
  homEquiv_comp g h := by
    change (Scheme.ProEt.topology Y).uliftYonedaEquiv
        ((((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).homEquiv _ _) (h ≫ g)) = _
    rw [Adjunction.homEquiv_naturality_right,
      GrothendieckTopology.uliftYonedaEquiv_comp]
    rfl

/-- The base-changed site object directly corepresents the same evaluation functor. -/
def proEtBaseChangeEvaluationCorepresentative :
    ((sheafSections (Scheme.ProEt.topology X) (Type (u + 1))).obj
      (op ((ProetalePullback.Construction.proEtBaseChange f).obj U))).CorepresentableBy
        ((Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj ((ProetalePullback.Construction.proEtBaseChange f).obj U)) where
  homEquiv := (Scheme.ProEt.topology X).uliftYonedaEquiv
  homEquiv_comp g h := (Scheme.ProEt.topology X).uliftYonedaEquiv_comp h g

/-- The inverse image of a represented sheaf is represented by the actual base-changed scheme. -/
def proEtPullbackRepresentableIso :
    (PullbackTypes.Construction.proEtTypeSheafPullback f).obj ((Scheme.ProEt.topology Y).uliftYoneda.{u + 1}.obj U) ≅
      (Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj ((ProetalePullback.Construction.proEtBaseChange f).obj U) :=
  (proEtPullbackEvaluationCorepresentative f U).uniqueUpToIso
    (proEtBaseChangeEvaluationCorepresentative f U)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackRepresentable.Construction
