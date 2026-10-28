import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ChernFrames
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalLog
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicFrameComparison
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationDolbeaultSub
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticPullbackTransitions
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation

/-! # Translation Cover -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! An actual common native cover carries a vector lift, a translated
algebraic theta frame, and an original algebraic theta frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (PolarizationFactor.Geometric.polarizationFactor F hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationCover_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationCover_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationMap (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) : M.abelian.toOver ⟶ M.abelian.toOver :=
  RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian (M.vectorPeriod a)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationMap_period (a w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.thetaTranslationMap a) (M.vectorPeriod w) = M.vectorPeriod (w + a) :=
  (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation_period M.abelian M.period M.period_add (QuotientAddGroup.mk a) (QuotientAddGroup.mk w)).trans
    (congrArg M.period (QuotientAddGroup.mk_add (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice.toAddSubgroup w a).symm)

abbrev PeriodModel.Geometric.AlgebraicPeriodModel.ThetaTranslationCoverIndex := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
  (RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension ×
    RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)

def PeriodModel.Geometric.AlgebraicPeriodModel.translatedThetaFrame (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame ((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback (M.thetaTranslationMap a).left).sheaf :=
  AbelianModuli.ReferenceFamily.Local.PullbackFrames.pullbackLocalFrame (M.thetaTranslationMap a).left (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).sheaf
    (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i)

def PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationCover (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (i : M.ThetaTranslationCoverIndex U V) :
    Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  (M.localPeriodDomain i.1 ⊓ AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (M.translatedThetaFrame U V f g a i.2.1)) ⊓
    AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i.2.2)

include hf hg in
theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationCover_covers (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    ∃ i, q ∈ M.thetaTranslationCover U V f g a i := by
  obtain ⟨i, hi⟩ := M.thetaLocalLineFrame_cover U V f g hf hg
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.thetaTranslationMap a) q)
  obtain ⟨j, hj⟩ := M.thetaLocalLineFrame_cover U V f g hf hg q
  exact ⟨(q, (i, j)), ⟨M.mem_localPeriodDomain q, hi⟩, hj⟩

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationCover_period_subset (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (i : M.ThetaTranslationCoverIndex U V) :
    M.thetaTranslationCover U V f g a i ≤ M.localPeriodDomain i.1 := inf_le_left.trans inf_le_left

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationCover_source_subset (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (i : M.ThetaTranslationCoverIndex U V) :
    M.thetaTranslationCover U V f g a i ≤
      AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (M.translatedThetaFrame U V f g a i.2.1) :=
  inf_le_left.trans inf_le_right

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationCover_target_subset (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (i : M.ThetaTranslationCoverIndex U V) :
    M.thetaTranslationCover U V f g a i ≤
      AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i.2.2) := inf_le_right

include hf hg in
theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationCover_target_lift (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (i : M.ThetaTranslationCoverIndex U V)
    (q : M.thetaTranslationCover U V f g a i) :
    M.localPeriodLift i.1 q.val ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i.2.2 := by
  apply (M.thetaFrameOpen_period U V f g hf hg i.2.2 (M.localPeriodLift i.1 q.val)).mp
  have he := M.localPeriodLift_period i.1 q.val q.property.1.1
  exact (congrArg (fun x => x ∈ AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation
    (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i.2.2)) he).mpr q.property.2

include hf hg in
theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationCover_source_lift (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (i : M.ThetaTranslationCoverIndex U V)
    (q : M.thetaTranslationCover U V f g a i) :
    M.localPeriodLift i.1 q.val + a ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i.2.1 := by
  apply (M.thetaFrameOpen_period U V f g hf hg i.2.1 (M.localPeriodLift i.1 q.val + a)).mp
  have he := (M.thetaTranslationMap_period a (M.localPeriodLift i.1 q.val)).symm.trans
    (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.thetaTranslationMap a))
      (M.localPeriodLift_period i.1 q.val q.property.1.1))
  exact (congrArg (fun x => x ∈ AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation
    (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i.2.1)) he).mpr q.property.1.2

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
