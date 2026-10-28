import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ChernFrames
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalLog
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveLogarithmicCover

/-! # Chern Smooth -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The actual native theta transitions and their constructed continuous
logarithms are holomorphic in the original native manifold structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open Filter _root_.Topology
open scoped _root_.Manifold ContDiff

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaChernSmooth_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaChernSmooth_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

include hf hg in
theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaFrameTransition_holomorphic
    (i j : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    ContMDiff 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℂ, ℂ) ∞
      (AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameTransitionPair M.abelian.variety.presentation
        (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i) (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left j)) := by
  let A := AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i) ⊓
    AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left j)
  intro p
  let w : A → (ProjectivePeriodData.Geometric.projectivePeriodData F).space := fun q => M.localPeriodLift p.val q.val
  have hw : ContMDiffAt 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space) ∞ w p :=
    (M.localPeriodLift_contMDiffAt p.val p.val (M.mem_localPeriodDomain p.val)).comp p
      (contMDiff_subtype_val (I := 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) (n := ∞) p)
  have hperiod (q : A) (hq : q.val ∈ M.localPeriodDomain p.val) : M.vectorPeriod (w q) = q.val :=
    M.localPeriodLift_period p.val q.val hq
  have hwi (q : A) (hq : q.val ∈ M.localPeriodDomain p.val) : w q ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i := by
    apply (M.thetaFrameOpen_period U V f g hf hg i (w q)).mp
    exact (congrArg (fun x => x.left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      RepresentationTheory.Theta.Geometric.ProductFrames.thetaQuotientOpen f.left g.left i.1 i.2) (hperiod q hq)).mpr q.property.1
  have hwj (q : A) (hq : q.val ∈ M.localPeriodDomain p.val) : w q ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V j := by
    apply (M.thetaFrameOpen_period U V f g hf hg j (w q)).mp
    exact (congrArg (fun x => x.left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      RepresentationTheory.Theta.Geometric.ProductFrames.thetaQuotientOpen f.left g.left j.1 j.2) (hperiod q hq)).mpr q.property.2
  have h₀ := M.mem_localPeriodDomain p.val
  have hrat := (((LocalLog.Geometric.thetaGauge_contDiffAt F) hP U V j (w p) (hwj p h₀)).div
    ((LocalLog.Geometric.thetaGauge_contDiffAt F) hP U V i (w p) (hwi p h₀))
    (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero U V i.1 i.2 (w p) (hwi p h₀).1 (hwi p h₀).2)).contMDiffAt.comp p hw
  apply hrat.congr_of_eventuallyEq
  have hn := continuous_subtype_val.continuousAt.preimage_mem_nhds
    ((M.localPeriodDomain p.val).isOpen.mem_nhds h₀)
  filter_upwards [hn] with q hq
  have ht := M.thetaLocalLineFrame_period_transition U V f g hf hg i j (w q) (hwi q hq) (hwj q hq)
  have he : (⟨M.vectorPeriod (w q),
      (M.thetaFrameOpen_period U V f g hf hg i (w q)).mpr (hwi q hq),
      (M.thetaFrameOpen_period U V f g hf hg j (w q)).mpr (hwj q hq)⟩ : A) = q :=
    Subtype.ext (hperiod q hq)
  exact (congrArg (AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameTransitionPair M.abelian.variety.presentation
    (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i) (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left j)) he).symm.trans ht

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaChernLogRefinement_holomorphic
    (a b : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver × RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    ContMDiff 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℂ, ℂ) ∞
      ((M.thetaChernLogRefinement U V f g hf hg).logarithm a b) :=
  ComplexMultiplication.HodgeComparison.ProjectiveLogarithmicCover.CM.Construction.logarithmicRefinement_holomorphic _ _
    (M.thetaFrameTransition_holomorphic U V f g hf hg) (M.thetaChernLogRefinement U V f g hf hg) a b

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
