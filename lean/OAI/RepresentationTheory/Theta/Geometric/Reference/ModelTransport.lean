import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.Transport
import OAI.RepresentationTheory.Theta.Geometric.Period.Models
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel

/-! # Model Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Every constructed GeometricTheta period model is a ReferenceFamily reference model on
the same abelian variety, with the same integral algebraic action. The
change of period coordinates is proved on the original quotient maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x : D.domain}

section

variable (F : D.ReferenceAnalyticFiber x)

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.canonicalTorusEquiv_action (a : NumberField.RingOfIntegers E)
    (t : (D.canonicalPeriodData hg x).periodTorus) :
    F.canonicalTorusDiffeomorph D hg (D.canonicalQuotientAction hg x a t) =
      (F.toNativeReference D).quotientAction hg.reference_admissible a
        (F.canonicalTorusDiffeomorph D hg t) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact congrArg (QuotientAddGroup.mk : Data.ActiveHeckeThetaData.referenceTangent (s := s) →
    (F.toNativeReference D).periodData.periodTorus) (F.periodComparison_action D hg a v)

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.canonicalTorusEquiv_symm_action (a : NumberField.RingOfIntegers E)
    (t : (F.toNativeReference D).periodData.periodTorus) :
    (F.canonicalTorusDiffeomorph D hg).symm
      ((F.toNativeReference D).quotientAction hg.reference_admissible a t) =
        D.canonicalQuotientAction hg x a ((F.canonicalTorusDiffeomorph D hg).symm t) := by
  apply (F.canonicalTorusDiffeomorph D hg).injective
  exact ((F.canonicalTorusDiffeomorph D hg).apply_symm_apply _).trans
    ((F.canonicalTorusEquiv_action a ((F.canonicalTorusDiffeomorph D hg).symm t)).trans
      (congrArg ((F.toNativeReference D).quotientAction hg.reference_admissible a)
        ((F.canonicalTorusDiffeomorph D hg).apply_symm_apply t))).symm

end

variable (M : D.PeriodModel hg x) (F : D.ReferenceAnalyticFiber x)

local instance Data.ActiveHeckeThetaData.PeriodModel.referenceTransport_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Data.ActiveHeckeThetaData.PeriodModel.referenceTransport_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def Data.ActiveHeckeThetaData.PeriodModel.toNativeReferenceModel :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel (F.toNativeReference D) hg.reference_admissible where
  abelian := M.abelian
  period := (F.canonicalTorusDiffeomorph D hg).symm.trans M.period
  functorAction := M.action
  period_add u v := by
    change M.period ((F.canonicalTorusEquiv D hg).symm (u + v)) = _
    rw [map_add, M.period_add]
    rfl
  period_action a t := by
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.action a))
      (M.period ((F.canonicalTorusDiffeomorph D hg).symm t)) = _
    rw [M.period_action]
    exact congrArg M.period (F.canonicalTorusEquiv_symm_action a t).symm

theorem Data.ActiveHeckeThetaData.PeriodModel.toNativeReferenceModel_period (t : (D.canonicalPeriodData hg x).periodTorus) :
    (M.toNativeReferenceModel F).period (F.canonicalTorusDiffeomorph D hg t) = M.period t :=
  congrArg M.period ((F.canonicalTorusDiffeomorph D hg).symm_apply_apply t)

theorem Data.ActiveHeckeThetaData.PeriodModel.toNativeReferenceModel_vectorPeriod (v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    (M.toNativeReferenceModel F).period (QuotientAddGroup.mk (F.periodComparison D hg v)) =
      M.period (QuotientAddGroup.mk v) :=
  M.toNativeReferenceModel_period F (QuotientAddGroup.mk v)

theorem Data.ActiveHeckeThetaData.PeriodModel.toNativeReferenceModel_action (a : NumberField.RingOfIntegers E) :
    (M.toNativeReferenceModel F).functorAction a = M.action a := rfl

end

end OAI.RepresentationTheory.Theta.Geometric
