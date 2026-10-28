import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.IntrinsicMetric
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.ChernComparison

/-! # Chern Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! Actual theta frames form an atlas of the original algebraic line
bundle. ChernClass's evaluated transition is precisely the theta gauge ratio. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def ReferenceTheta.ChernFrames.thetaLocalLineFrame {X : Scheme.{0}} {n m : ℕ}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m) (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex n m) :
    LineFrameAtlas.LocalLineFrame (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f g).sheaf where
  domain := RepresentationTheory.Theta.Geometric.ProductFrames.thetaQuotientOpen f g i.1 i.2
  frame := RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.thetaQuotientIndexedFrame f g i _ le_rfl

theorem ReferenceTheta.ChernFrames.thetaLocalLineFrame_restrict {X : Scheme.{0}} {n m : ℕ}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m) (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex n m)
    (W : X.Opens) (hW : W ≤ (ReferenceTheta.ChernFrames.thetaLocalLineFrame f g i).domain) :
    SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hW (ReferenceTheta.ChernFrames.thetaLocalLineFrame f g i).frame =
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.thetaQuotientIndexedFrame f g i W hW :=
  RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.thetaQuotientIndexedFrame_restrict f g i hW le_rfl

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

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaChernFrames_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaChernFrames_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaLocalLineFrame_cover (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    ∃ i, p ∈ AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i) := by
  obtain ⟨t, rfl⟩ := M.period.surjective p
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨i, hi⟩ := RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen_cover U V w
  exact ⟨i, (M.thetaFrameOpen_period U V f g hf hg i w).mpr hi⟩

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaLocalLineFrame_period_transition
    (i j : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : F.periodData.space)
    (hi : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) (hj : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V j) :
    AnalyticFrameTransitions.framePointTransition M.abelian.variety.presentation
      (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i) (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left j) (M.vectorPeriod w)
      ((M.thetaFrameOpen_period U V f g hf hg i w).mpr hi)
      ((M.thetaFrameOpen_period U V f g hf hg j w).mpr hj) =
      RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V j.1 j.2 w / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w := by
  let W := RepresentationTheory.Theta.Geometric.ProductFrames.thetaQuotientOpen f.left g.left i.1 i.2 ⊓ RepresentationTheory.Theta.Geometric.ProductFrames.thetaQuotientOpen f.left g.left j.1 j.2
  have hw : (M.vectorPeriod w).left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W :=
    ⟨(M.thetaFrameOpen_period U V f g hf hg i w).mpr hi,
      (M.thetaFrameOpen_period U V f g hf hg j w).mpr hj⟩
  have he := Intrinsic.FrameEvaluation.framePointTransition_native M.abelian.variety.presentation
    (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i) (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left j)
    W inf_le_left inf_le_right ⟨M.vectorPeriod w, hw⟩
  erw [ReferenceTheta.ChernFrames.thetaLocalLineFrame_restrict, ReferenceTheta.ChernFrames.thetaLocalLineFrame_restrict] at he
  exact he.trans (RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.thetaQuotientIndexedFrame_transition_value U V f g
    (M.vectorPeriod w) w (hf _) (hg _) i j W inf_le_left inf_le_right hw)

end

/-! A constructed open refinement carries logarithms of the actual
theta frame transitions and computes the original native Chern class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

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

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaChernLogs_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaChernLogs_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaChernLogRefinement : DivisorClass.Chern.LogRefinementOpen.Construction.LogarithmicRefinement
    (fun i => AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i))
    (fun i j => AnalyticFrameTransitions.frameTransitionPair M.abelian.variety.presentation
      (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i) (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left j)) :=
  Classical.choice (DivisorClass.Chern.LogRefinementOpen.Construction.nonempty_logarithmicRefinement _ (M.thetaLocalLineFrame_cover U V f g hf hg)
    _ (fun i j p => AnalyticFrameTransitions.frameTransitionPair_ne_zero M.abelian.variety.presentation
      (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i) (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left j) p))

abbrev Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaChernCover := (M.thetaChernLogRefinement U V f g hf hg).cover

def Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaChernLogCech : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (M.thetaChernCover U V f g hf hg) := fun a =>
  ((M.thetaChernLogRefinement U V f g hf hg).logarithm (a 0) (a 1)).comp
    (DivisorClass.Chern.LogRefinementOpen.Construction.openInclusionMap (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1)))

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaChernLogCech_exp
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) :
    Complex.exp (M.thetaChernLogCech U V f g hf hg a p) =
      AnalyticFrameTransitions.framePointTransition M.abelian.variety.presentation
        (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left (a 0).2) (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left (a 1).2) p.val
        ((M.thetaChernLogRefinement U V f g hf hg).subset (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0 p.property))
        ((M.thetaChernLogRefinement U V f g hf hg).subset (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1 p.property)) :=
  (M.thetaChernLogRefinement U V f g hf hg).exp_logarithm (a 0) (a 1)
    ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0 p.property, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1 p.property⟩

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaChernLogCech_cocycle : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) (M.thetaChernCover U V f g hf hg)
    (M.thetaChernLogCech U V f g hf hg) :=
  Frame.ChernComparison.frameLog_exponentialCocycle (X := M.abelian.variety.presentation)
    (M := (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).sheaf)
    (M.thetaChernCover U V f g hf hg) (fun i => ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i.2)
    (M.thetaChernLogRefinement U V f g hf hg).subset _ (M.thetaChernLogCech_exp U V f g hf hg)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaChernClass_eq_logarithmic :
    Intrinsic.ChernClasses.lineBundleChernClass M.abelian.variety.presentation (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) =
      DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
        (M.thetaChernCover U V f g hf hg) (M.thetaChernLogRefinement U V f g hf hg).covers
        (M.thetaChernLogCech U V f g hf hg) (M.thetaChernLogCech_cocycle U V f g hf hg) :=
  Frame.ChernComparison.firstChernClass_eq_frameLogs
    (Intrinsic.ChernClasses.nativeLineBundle M.abelian.variety.presentation (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left))
    (M.thetaChernCover U V f g hf hg) (M.thetaChernLogRefinement U V f g hf hg).covers
    (fun i => ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i.2) (M.thetaChernLogRefinement U V f g hf hg).subset
    _ _ (M.thetaChernLogCech_exp U V f g hf hg)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
