import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.NowhereZeroUnit

/-! # Translation Gauges -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Actual holomorphic theta gauges on the native common cover compare
translated and original algebraic frames with local period lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.NowhereZeroUnit

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (PolarizationFactor.Geometric.polarizationFactor F hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationGauges_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationGauges_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationCover_lift_holomorphic (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (i : M.ThetaTranslationCoverIndex U V) :
    ContMDiff 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space) ∞
      (fun q : M.thetaTranslationCover U V f g a i => M.localPeriodLift i.1 q.val) := by
  intro q
  exact (M.localPeriodLift_contMDiffAt i.1 q.val q.property.1.1).comp q
    (contMDiff_subtype_val (I := 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) (n := ∞) q)

def PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationSourceGauge (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (i : M.ThetaTranslationCoverIndex U V) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M := M.thetaTranslationCover U V f g a i) where
  val q := RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.2.1.1 i.2.1.2 (M.localPeriodLift i.1 q.val + a)
  property := by
    intro q
    have hm := M.thetaTranslationCover_source_lift U V f g hf hg a i q
    exact (LocalLog.Geometric.thetaGauge_contDiffAt F hP U V i.2.1 _ hm).contMDiffAt.comp q
      (((M.thetaTranslationCover_lift_holomorphic U V f g a i).add contMDiff_const) q)

def PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationTargetGauge (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (i : M.ThetaTranslationCoverIndex U V) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M := M.thetaTranslationCover U V f g a i) where
  val q := RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.2.2.1 i.2.2.2 (M.localPeriodLift i.1 q.val)
  property := by
    intro q
    have hm := M.thetaTranslationCover_target_lift U V f g hf hg a i q
    exact (LocalLog.Geometric.thetaGauge_contDiffAt F hP U V i.2.2 _ hm).contMDiffAt.comp q
      (M.thetaTranslationCover_lift_holomorphic U V f g a i q)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationSourceGauge_ne_zero (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (i : M.ThetaTranslationCoverIndex U V)
    (q : M.thetaTranslationCover U V f g a i) : M.thetaTranslationSourceGauge U V f g hf hg a i q ≠ 0 :=
  RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero U V i.2.1.1 i.2.1.2 _
    (M.thetaTranslationCover_source_lift U V f g hf hg a i q).1
    (M.thetaTranslationCover_source_lift U V f g hf hg a i q).2

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationTargetGauge_ne_zero (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (i : M.ThetaTranslationCoverIndex U V)
    (q : M.thetaTranslationCover U V f g a i) : M.thetaTranslationTargetGauge U V f g hf hg a i q ≠ 0 :=
  RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero U V i.2.2.1 i.2.2.2 _
    (M.thetaTranslationCover_target_lift U V f g hf hg a i q).1
    (M.thetaTranslationCover_target_lift U V f g hf hg a i q).2

def PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationGaugeUnit (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (i : M.ThetaTranslationCoverIndex U V) :
    (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M := M.thetaTranslationCover U V f g a i))ˣ :=
  AbelianModuli.ReferenceFamily.Holomorphic.NowhereZeroUnit.holomorphicUnitOfNowhereZero _ _ (M.thetaTranslationSourceGauge U V f g hf hg a i)
      (M.thetaTranslationSourceGauge_ne_zero U V f g hf hg a i) /
    AbelianModuli.ReferenceFamily.Holomorphic.NowhereZeroUnit.holomorphicUnitOfNowhereZero _ _ (M.thetaTranslationTargetGauge U V f g hf hg a i)
      (M.thetaTranslationTargetGauge_ne_zero U V f g hf hg a i)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationGaugeUnit_value (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (i : M.ThetaTranslationCoverIndex U V)
    (q : M.thetaTranslationCover U V f g a i) :
    (M.thetaTranslationGaugeUnit U V f g hf hg a i).val q =
      RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.2.1.1 i.2.1.2 (M.localPeriodLift i.1 q.val + a) /
        RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.2.2.1 i.2.2.2 (M.localPeriodLift i.1 q.val) :=
  AbelianModuli.ReferenceFamily.Holomorphic.LogUnitClass.holomorphicUnit_value_div (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (M.thetaTranslationCover U V f g a i) _ _ q

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
