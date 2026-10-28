import OAI.AlgebraicGeometry.PELModuli.CMPoints.Generic
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentFieldLift
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentHeightBound
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coproduct

/-! # Component Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The IntegralModel components give actual open pieces of the arithmetic
moduli space used by CMAbelianVariety. Descent therefore retains the chosen component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

abbrev Models.RankThreePELModel.genericComponent (a : M.Family) (t : Fin (M.componentCount a)) :=
  (Over.pullback M.arithmetic.generic).obj ((M.components a).S t)

def Models.RankThreePELModel.genericComponentInclusion (a : M.Family) (t : Fin (M.componentCount a)) :
    M.genericComponent a t ⟶ M.reducedGenericModuli a :=
  (Over.pullback M.arithmetic.generic).map (M.integralComponentInclusion a t) ≫
    (M.integral a).genericIso.hom

instance Models.RankThreePELModel.genericComponentInclusion_open (a : M.Family) (t : Fin (M.componentCount a)) :
    IsOpenImmersion (M.genericComponentInclusion a t).left := by
  have : IsOpenImmersion (M.integralComponentInclusion a t).left :=
    IntegralModel.Coproduct.decomposition_inclusion_open (M.components a).S (M.decomposition a) t
  have : IsOpenImmersion ((Over.pullback M.arithmetic.generic).map (M.integralComponentInclusion a t)).left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) _ _ inferInstance
  have : IsIso (M.integral a).genericIso.hom.left := inferInstanceAs
    (IsIso (((Over.forget (Spec (.of M.arithmetic.extension.carrier))).mapIso (M.integral a).genericIso).hom))
  change IsOpenImmersion (_ ≫ _)
  infer_instance

abbrev Models.RankThreePELModel.embeddedGenericComponent (a : M.Family) (t : Fin (M.componentCount a)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom M.arithmetic.embedding.rangeRestrictField))).obj
    (M.genericComponent a t)

def Models.RankThreePELModel.embeddedGenericComponentInclusion (a : M.Family) (t : Fin (M.componentCount a)) :
    M.embeddedGenericComponent a t ⟶ M.embeddedReducedGenericModuli a :=
  (Over.pullback (Spec.map (CommRingCat.ofHom M.arithmetic.embedding.rangeRestrictField))).map
    (M.genericComponentInclusion a t)

instance Models.RankThreePELModel.embeddedGenericComponentInclusion_open (a : M.Family) (t : Fin (M.componentCount a)) :
    IsOpenImmersion (M.embeddedGenericComponentInclusion a t).left :=
  MorphismProperty.overPullbackMap (P := @IsOpenImmersion) _ _ inferInstance

theorem Models.RankThreePELModel.component_CM_point_descends (hCMAbelianVariety : Descent.ModuliInput) (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (t : Fin (M.componentCount a))
    (z : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ (M.embeddedGenericComponent a t).left)
    (hCM : ((M.genericStandardModuli hM a).abelianAt
      (z ≫ (M.embeddedGenericComponentInclusion a t).left)).HasCMH1) :
    ∃ F : Subfield ℂ, NumberField F ∧
      ∃ p : Spec (.of F) ⟶ (M.embeddedGenericComponent a t).left,
        Spec.map (CommRingCat.ofHom F.subtype) ≫ p = z :=
  @ComponentFieldLift.CM_point_descends_on_open_component hCMAbelianVariety (M.genericStandardModuli hM a)
    (M.embeddedGenericComponent a t).left (M.embeddedGenericComponentInclusion a t).left
    (M.embeddedGenericComponentInclusion_open a t) z hCM

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
