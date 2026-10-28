import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.TranslationGauges
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicPicardHomomorphism

/-! # Translation Of -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! The translated algebraic theta bundle minus the original one has
an actual closed cocycle on the constructed common native cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

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

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationCocycle_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationCocycle_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationCocycle_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

def Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationSourceCech (a : F.periodData.space) :
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj (M.thetaTranslationCover U V f g a) 1 :=
  Intrinsic.FrameUnitCocycle.frameUnitCech M.abelian.variety (M.thetaTranslationCover U V f g a)
    (fun i => M.translatedThetaFrame U V f g a i.2.1) (M.thetaTranslationCover_source_subset U V f g a)

def Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationTargetCech (a : F.periodData.space) :
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj (M.thetaTranslationCover U V f g a) 1 :=
  Intrinsic.FrameUnitCocycle.frameUnitCech M.abelian.variety (M.thetaTranslationCover U V f g a)
    (fun i => ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i.2.2) (M.thetaTranslationCover_target_subset U V f g a)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationSourceCech_closed (a : F.periodData.space) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj (M.thetaTranslationCover U V f g a) 1
      (M.thetaTranslationSourceCech U V f g a) = 0 :=
  Intrinsic.FrameUnitCocycle.frameUnitCech_closed M.abelian.variety (M.thetaTranslationCover U V f g a)
    (fun i => M.translatedThetaFrame U V f g a i.2.1) (M.thetaTranslationCover_source_subset U V f g a)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationTargetCech_closed (a : F.periodData.space) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj (M.thetaTranslationCover U V f g a) 1
      (M.thetaTranslationTargetCech U V f g a) = 0 :=
  Intrinsic.FrameUnitCocycle.frameUnitCech_closed M.abelian.variety (M.thetaTranslationCover U V f g a)
    (fun i => ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i.2.2) (M.thetaTranslationCover_target_subset U V f g a)

def Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationDifferenceCech (a : F.periodData.space) :
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj (M.thetaTranslationCover U V f g a) 1 :=
  M.thetaTranslationSourceCech U V f g a - M.thetaTranslationTargetCech U V f g a

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationDifferenceCech_closed (a : F.periodData.space) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj (M.thetaTranslationCover U V f g a) 1
      (M.thetaTranslationDifferenceCech U V f g a) = 0 :=
  Cech.Add.cechSub_closed (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) (M.thetaTranslationCover U V f g a)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj 1
    _ _ (M.thetaTranslationSourceCech_closed U V f g a) (M.thetaTranslationTargetCech_closed U V f g a)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationDifferenceCech_class (a : F.periodData.space) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
      (M.thetaTranslationCover U V f g a)
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
      (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
        (M.thetaTranslationCover U V f g a) (M.thetaTranslationCover_covers U V f g hf hg a)) 0
      (M.thetaTranslationDifferenceCech U V f g a) (M.thetaTranslationDifferenceCech_closed U V f g a) =
      Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety
        (((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback (M.thetaTranslationMap a).left).tensor
          (Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left))) := by
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  let W := M.thetaTranslationCover U V f g a
  let S := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  let : AddCommGroup (CategoryTheory.Sheaf.H S 1) := Cech.Add.cechClassAddCommGroup (X := T) S 1
  let : AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology M.abelian.variety.analyticModel M.abelian.variety.analyticSpace) :=
    Cech.Add.cechClassAddCommGroup (X := TopCat.of M.abelian.variety.analyticSpace)
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf M.abelian.variety.analyticModel M.abelian.variety.analyticSpace) 1
  have hW := M.thetaTranslationCover_covers U V f g hf hg a
  have hs := Cech.Add.cechSheafClass_sub (X := T) W S (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := T) W hW) 0
    (M.thetaTranslationSourceCech U V f g a) (M.thetaTranslationTargetCech U V f g a)
    (M.thetaTranslationSourceCech_closed U V f g a) (M.thetaTranslationTargetCech_closed U V f g a)
  have hL := Intrinsic.FrameUnitCocycle.nativeHolomorphicLineClass_frameUnits M.abelian.variety W
    ((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback (M.thetaTranslationMap a).left)
    (fun i => M.translatedThetaFrame U V f g a i.2.1) (M.thetaTranslationCover_source_subset U V f g a) hW
  have hR := Intrinsic.FrameUnitCocycle.nativeHolomorphicLineClass_frameUnits M.abelian.variety W
    (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) (fun i => ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i.2.2)
    (M.thetaTranslationCover_target_subset U V f g a) hW
  exact hs.trans ((congrArg₂ (fun x y : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology
    M.abelian.variety.analyticModel M.abelian.variety.analyticSpace => x - y) hL.symm hR.symm).trans
    (Intrinsic.HolomorphicPicardHomomorphism.nativeHolomorphicLineClass_tensor_dual M.abelian.variety
      ((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback (M.thetaTranslationMap a).left)
      (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)).symm)

end

section

/-! Evaluate the actual translated and original theta-frame cocycles
at any vector lift of a point of their common native cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

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

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationValues_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationValues_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaFrameTransition_of_period
    (i j : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (w : F.periodData.space) (q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (hw : M.vectorPeriod w = q)
    (hi : q ∈ AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i))
    (hj : q ∈ AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left j)) :
    AnalyticFrameTransitions.framePointTransition M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i)
      (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left j) q hi hj = RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V j.1 j.2 w / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w := by
  subst q
  exact M.thetaLocalLineFrame_period_transition U V f g hf hg i j w
    ((M.thetaFrameOpen_period U V f g hf hg i w).mp hi)
    ((M.thetaFrameOpen_period U V f g hf hg j w).mp hj)

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationSourceCech_period_value (a : F.periodData.space)
    (b : Fin 2 → M.ThetaTranslationCoverIndex U V) (q : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaTranslationCover U V f g a) b)
    (w : F.periodData.space) (hw : M.vectorPeriod w = q.val) :
    (Holomorphic.LogUnitClass.holomorphicUnitSection (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaTranslationCover U V f g a) b) (M.thetaTranslationSourceCech U V f g a b)).val q =
      RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V (b 1).2.1.1 (b 1).2.1.2 (w + a) /
        RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V (b 0).2.1.1 (b 0).2.1.2 (w + a) := by
  have h0 := M.thetaTranslationCover_source_subset U V f g a (b 0)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (M.thetaTranslationCover U V f g a) b 0 q.property)
  have h1 := M.thetaTranslationCover_source_subset U V f g a (b 1)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (M.thetaTranslationCover U V f g a) b 1 q.property)
  have hperiod := (M.thetaTranslationMap_period a w).symm.trans
    (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.thetaTranslationMap a)) hw)
  have hv := Intrinsic.FrameUnitCocycle.frameUnitCech_value M.abelian.variety (M.thetaTranslationCover U V f g a)
    (fun i => M.translatedThetaFrame U V f g a i.2.1) (M.thetaTranslationCover_source_subset U V f g a) b q
  exact hv.trans ((AnalyticPullbackTransitions.pullbackFrame_pointTransition (M.thetaTranslationMap a)
    (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left (b 0).2.1) (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left (b 1).2.1)
    q.val h0 h1).trans (M.thetaFrameTransition_of_period U V f g hf hg (b 0).2.1 (b 1).2.1
      (w + a) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.thetaTranslationMap a) q.val) hperiod h0 h1))

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationTargetCech_period_value (a : F.periodData.space)
    (b : Fin 2 → M.ThetaTranslationCoverIndex U V) (q : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaTranslationCover U V f g a) b)
    (w : F.periodData.space) (hw : M.vectorPeriod w = q.val) :
    (Holomorphic.LogUnitClass.holomorphicUnitSection (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaTranslationCover U V f g a) b) (M.thetaTranslationTargetCech U V f g a b)).val q =
      RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V (b 1).2.2.1 (b 1).2.2.2 w /
        RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V (b 0).2.2.1 (b 0).2.2.2 w := by
  have h0 := M.thetaTranslationCover_target_subset U V f g a (b 0)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (M.thetaTranslationCover U V f g a) b 0 q.property)
  have h1 := M.thetaTranslationCover_target_subset U V f g a (b 1)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (M.thetaTranslationCover U V f g a) b 1 q.property)
  exact (Intrinsic.FrameUnitCocycle.frameUnitCech_value M.abelian.variety (M.thetaTranslationCover U V f g a)
    (fun i => ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i.2.2) (M.thetaTranslationCover_target_subset U V f g a) b q).trans
      (M.thetaFrameTransition_of_period U V f g hf hg (b 0).2.2 (b 1).2.2 w q.val hw h0 h1)

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationDifferenceCech_period_value (a : F.periodData.space)
    (b : Fin 2 → M.ThetaTranslationCoverIndex U V) (q : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaTranslationCover U V f g a) b)
    (w : F.periodData.space) (hw : M.vectorPeriod w = q.val) :
    (Holomorphic.LogUnitClass.holomorphicUnitSection (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaTranslationCover U V f g a) b) (M.thetaTranslationDifferenceCech U V f g a b)).val q =
      (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V (b 1).2.1.1 (b 1).2.1.2 (w + a) /
        RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V (b 0).2.1.1 (b 0).2.1.2 (w + a)) /
      (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V (b 1).2.2.1 (b 1).2.2.2 w /
        RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V (b 0).2.2.1 (b 0).2.2.2 w) :=
  (Holomorphic.LogUnitClass.holomorphicUnitSection_value_sub (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaTranslationCover U V f g a) b)
    (M.thetaTranslationSourceCech U V f g a b) (M.thetaTranslationTargetCech U V f g a b) q).trans
      (congrArg₂ (· / ·) (M.thetaTranslationSourceCech_period_value U V f g hf hg a b q w hw)
        (M.thetaTranslationTargetCech_period_value U V f g hf hg a b q w hw))

end

section

/-! The actual theta ratio has the original translation character.
Its ratios at one common lift are exactly the algebraic difference
cocycle values, with no choices of logarithms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationRatios_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationRatios_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationRatio (a : F.periodData.space) (i : M.ThetaTranslationCoverIndex U V) (w : F.periodData.space) : ℂ :=
  RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.2.1.1 i.2.1.2 (w + a) / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.2.2.1 i.2.2.2 w

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationRatio_translates (hdeg : V.degree = U.degree + 1)
    (a : F.periodData.space) (i : M.ThetaTranslationCoverIndex U V)
    (l : F.periodData.periodIntegerLattice) (w : F.periodData.space) :
    M.thetaTranslationRatio U V a i (w + l.val) =
      ((F.polarizationFactor hP).value l (w + a) / (F.polarizationFactor hP).value l w) *
        M.thetaTranslationRatio U V a i w := by
  change RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.2.1.1 i.2.1.2 (w + l.val + a) /
    RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.2.2.1 i.2.2.2 (w + l.val) = _
  rw [show w + l.val + a = (w + a) + l.val by abel,
    RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_translates U V hdeg, RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_translates U V hdeg]
  exact (div_mul_div_comm _ _ _ _).symm

variable (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationGaugeUnit_ratio (a : F.periodData.space) (i : M.ThetaTranslationCoverIndex U V)
    (q : M.thetaTranslationCover U V f g a i) :
    (M.thetaTranslationGaugeUnit U V f g hf hg a i).val q =
      M.thetaTranslationRatio U V a i (M.localPeriodLift i.1 q.val) :=
  M.thetaTranslationGaugeUnit_value U V f g hf hg a i q

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationDifferenceCech_ratio (a : F.periodData.space)
    (b : Fin 2 → M.ThetaTranslationCoverIndex U V) (q : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaTranslationCover U V f g a) b)
    (w : F.periodData.space) (hw : M.vectorPeriod w = q.val) :
    (Holomorphic.LogUnitClass.holomorphicUnitSection (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaTranslationCover U V f g a) b) (M.thetaTranslationDifferenceCech U V f g a b)).val q =
        M.thetaTranslationRatio U V a (b 1) w / M.thetaTranslationRatio U V a (b 0) w := by
  refine (M.thetaTranslationDifferenceCech_period_value U V f g hf hg a b q w hw).trans ?_
  unfold Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationRatio
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end

section

/-! The actual theta difference cocycle multiplied by the period
translation cocycle is the boundary of the constructed holomorphic
theta gauges. This fixes the sign of the native class comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

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

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaGaugeIdentity_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaGaugeIdentity_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationGaugeIdentity (hdeg : V.degree = U.degree + 1)
    (a : F.periodData.space) (b : Fin 2 → M.ThetaTranslationCoverIndex U V)
    (q : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaTranslationCover U V f g a) b) :
    (Holomorphic.LogUnitClass.holomorphicUnitSection (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaTranslationCover U V f g a) b)
      (M.thetaTranslationDifferenceCech U V f g a b)).val q *
        Complex.exp (M.localTranslationDifference a (b 0).1 (b 1).1
          ⟨q.val, M.thetaTranslationCover_period_subset U V f g a (b 0)
            (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ b 0 q.property),
            M.thetaTranslationCover_period_subset U V f g a (b 1)
              (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ b 1 q.property)⟩) =
      (M.thetaTranslationGaugeUnit U V f g hf hg a (b 1)).val
        ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ b 1 q.property⟩ /
      (M.thetaTranslationGaugeUnit U V f g hf hg a (b 0)).val
        ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ b 0 q.property⟩ := by
  let q' : ↥(M.localPeriodDomain (b 0).1 ⊓ M.localPeriodDomain (b 1).1) :=
    ⟨q.val, M.thetaTranslationCover_period_subset U V f g a (b 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ b 0 q.property),
      M.thetaTranslationCover_period_subset U V f g a (b 1)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ b 1 q.property)⟩
  have hw := M.localPeriodLift_period (b 0).1 q.val q'.property.1
  have hs : M.localPeriodLift (b 0).1 q.val + (M.localPeriodDifference (b 0).1 (b 1).1 q').val =
      M.localPeriodLift (b 1).1 q.val := by
    rw [M.localPeriodDifference_value]
    change M.localPeriodLift (b 0).1 q.val +
      (M.localPeriodLift (b 1).1 q.val - M.localPeriodLift (b 0).1 q.val) = _
    abel
  have ht := M.thetaTranslationRatio_translates U V hdeg a (b 1)
    (M.localPeriodDifference (b 0).1 (b 1).1 q') (M.localPeriodLift (b 0).1 q.val)
  rw [hs] at ht
  rw [M.thetaTranslationDifferenceCech_ratio U V f g hf hg a b q _ hw,
    M.thetaTranslationGaugeUnit_ratio U V f g hf hg,
    M.thetaTranslationGaugeUnit_ratio U V f g hf hg, ht,
    M.localTranslationDifference_exp]
  ring

end

/-! The original period translation cocycle on the actual common
theta cover, with its values and refinement-independent native class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

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

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaRefinedTranslation_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaRefinedTranslation_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaRefinedTranslationCech (a : F.periodData.space) :
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj (M.thetaTranslationCover U V f g a) 1 :=
  DivisorClass.Chern.Cech.AbelianRefinement.abelianCechRefinementMap (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    M.localPeriodDomain (M.thetaTranslationCover U V f g a) Prod.fst
    (M.thetaTranslationCover_period_subset U V f g a)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj 1
    (M.translationUnitCech a)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaRefinedTranslationCech_closed (a : F.periodData.space) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj (M.thetaTranslationCover U V f g a) 1
        (M.thetaRefinedTranslationCech U V f g a) = 0 :=
  DivisorClass.Chern.Cech.ClassRefinement.abelianCechRefinementMap_closed (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    M.localPeriodDomain (M.thetaTranslationCover U V f g a) Prod.fst
    (M.thetaTranslationCover_period_subset U V f g a)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj 1
    (M.translationUnitCech a) (M.translationUnitCech_closed a)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaRefinedTranslationCech_value (a : F.periodData.space)
    (b : Fin 2 → M.ThetaTranslationCoverIndex U V)
    (q : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaTranslationCover U V f g a) b) :
    (Holomorphic.LogUnitClass.holomorphicUnitSection (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaTranslationCover U V f g a) b)
      (M.thetaRefinedTranslationCech U V f g a b)).val q =
        Complex.exp (M.localTranslationDifference a (b 0).1 (b 1).1
          ⟨q.val, M.thetaTranslationCover_period_subset U V f g a (b 0)
            (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ b 0 q.property),
            M.thetaTranslationCover_period_subset U V f g a (b 1)
              (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ b 1 q.property)⟩) :=
  (Holomorphic.FrameClass.holomorphicUnitCech_refinement_value M.abelian.variety M.localPeriodDomain
    (M.thetaTranslationCover U V f g a) Prod.fst (M.thetaTranslationCover_period_subset U V f g a)
    (M.translationUnitCech a) b q).trans
      (M.translationUnitCech_value a (Prod.fst ∘ b)
        ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_refinement_le M.localPeriodDomain (M.thetaTranslationCover U V f g a)
          Prod.fst (M.thetaTranslationCover_period_subset U V f g a) b q.property⟩)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaRefinedTranslationCech_class (a : F.periodData.space) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
      (M.thetaTranslationCover U V f g a)
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
      (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
        (M.thetaTranslationCover U V f g a) (M.thetaTranslationCover_covers U V f g hf hg a)) 0
      (M.thetaRefinedTranslationCech U V f g a) (M.thetaRefinedTranslationCech_closed U V f g a) =
        M.translationHolomorphicClass a :=
  (DivisorClass.Chern.Cech.ClassRefinement.abelianCechSheafClass_refinement (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    M.localPeriodDomain (M.thetaTranslationCover U V f g a) Prod.fst
    (M.thetaTranslationCover_period_subset U V f g a)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    ((M.translationPrimitiveSystem a).liftCover _ _).iSup_domain
    (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
      (M.thetaTranslationCover U V f g a) (M.thetaTranslationCover_covers U V f g hf hg a)) 0
    (M.translationUnitCech a) (M.translationUnitCech_closed a)).trans (M.translationUnitCech_class a)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
