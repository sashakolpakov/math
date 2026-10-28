import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.HolomorphicClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.TranslationSub
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticPullbackTransitions
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation

/-! # Translation Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! An actual common native cover carries a vector lift, a translated
algebraic theta frame, and an original algebraic theta frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationCover_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationCover_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationMap (a : F.periodData.space) : M.abelian.toOver ⟶ M.abelian.toOver :=
  RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian (M.vectorPeriod a)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationMap_period (a w : F.periodData.space) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.thetaTranslationMap a) (M.vectorPeriod w) = M.vectorPeriod (w + a) :=
  (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation_period M.abelian M.period M.period_add (QuotientAddGroup.mk a) (QuotientAddGroup.mk w)).trans
    (congrArg M.period (QuotientAddGroup.mk_add F.periodData.periodIntegerLattice.toAddSubgroup w a).symm)

abbrev Reference.AlgebraicModel.ReferenceAlgebraicModel.ThetaTranslationCoverIndex := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
  (RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension ×
    RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)

def Reference.AlgebraicModel.ReferenceAlgebraicModel.translatedThetaFrame (a : F.periodData.space)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    LineFrameAtlas.LocalLineFrame ((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback (M.thetaTranslationMap a).left).sheaf :=
  Local.PullbackFrames.pullbackLocalFrame (M.thetaTranslationMap a).left (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).sheaf
    (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i)

def Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationCover (a : F.periodData.space) (i : M.ThetaTranslationCoverIndex U V) :
    Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  (M.localPeriodDomain i.1 ⊓ AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (M.translatedThetaFrame U V f g a i.2.1)) ⊓
    AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i.2.2)

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationCover_covers (a : F.periodData.space) (q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    ∃ i, q ∈ M.thetaTranslationCover U V f g a i := by
  obtain ⟨i, hi⟩ := M.thetaLocalLineFrame_cover U V f g hf hg
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.thetaTranslationMap a) q)
  obtain ⟨j, hj⟩ := M.thetaLocalLineFrame_cover U V f g hf hg q
  exact ⟨(q, (i, j)), ⟨M.mem_localPeriodDomain q, hi⟩, hj⟩

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationCover_period_subset (a : F.periodData.space) (i : M.ThetaTranslationCoverIndex U V) :
    M.thetaTranslationCover U V f g a i ≤ M.localPeriodDomain i.1 := inf_le_left.trans inf_le_left

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationCover_source_subset (a : F.periodData.space) (i : M.ThetaTranslationCoverIndex U V) :
    M.thetaTranslationCover U V f g a i ≤
      AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (M.translatedThetaFrame U V f g a i.2.1) :=
  inf_le_left.trans inf_le_right

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationCover_target_subset (a : F.periodData.space) (i : M.ThetaTranslationCoverIndex U V) :
    M.thetaTranslationCover U V f g a i ≤
      AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i.2.2) := inf_le_right

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationCover_target_lift (a : F.periodData.space) (i : M.ThetaTranslationCoverIndex U V)
    (q : M.thetaTranslationCover U V f g a i) :
    M.localPeriodLift i.1 q.val ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i.2.2 := by
  apply (M.thetaFrameOpen_period U V f g hf hg i.2.2 (M.localPeriodLift i.1 q.val)).mp
  have he := M.localPeriodLift_period i.1 q.val q.property.1.1
  exact (congrArg (fun x => x ∈ AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation
    (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i.2.2)) he).mpr q.property.2

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationCover_source_lift (a : F.periodData.space) (i : M.ThetaTranslationCoverIndex U V)
    (q : M.thetaTranslationCover U V f g a i) :
    M.localPeriodLift i.1 q.val + a ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i.2.1 := by
  apply (M.thetaFrameOpen_period U V f g hf hg i.2.1 (M.localPeriodLift i.1 q.val + a)).mp
  have he := (M.thetaTranslationMap_period a (M.localPeriodLift i.1 q.val)).symm.trans
    (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.thetaTranslationMap a))
      (M.localPeriodLift_period i.1 q.val q.property.1.1))
  exact (congrArg (fun x => x ∈ AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation
    (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i.2.1)) he).mpr q.property.1.2

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
