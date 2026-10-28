import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.Metric
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ModelDerivative

/-! # Intrinsic Metric -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! The Gaussian theta-frame weights descend to the actual period
quotient and then to the native complex points of the chosen model. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}

section

variable (F : Reference.Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP)) (hdeg : V.degree = U.degree + 1)

include hdeg in
theorem Reference.Fiber.ReferenceAnalyticFiber.thetaFrameMetricWeight_quotient_eq
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (v w : F.periodData.space)
    (h : (QuotientAddGroup.mk v : F.periodData.periodTorus) = QuotientAddGroup.mk w) :
    F.thetaFrameMetricWeight hP U V i v = F.thetaFrameMetricWeight hP U V i w := by
  have hl : v - w ∈ F.periodData.periodIntegerLattice.toAddSubgroup :=
    (@QuotientAddGroup.eq_iff_sub_mem F.periodData.space inferInstance
      F.periodData.periodIntegerLattice.toAddSubgroup inferInstance v w).mp h
  let l : F.periodData.periodIntegerLattice := ⟨v - w, hl⟩
  have hs : w + l.val = v := by dsimp only [l]; abel
  exact (congrArg (F.thetaFrameMetricWeight hP U V i) hs).symm.trans
    (F.thetaFrameMetricWeight_translates hP U V hdeg i l w)

def Reference.Fiber.ReferenceAnalyticFiber.thetaFrameMetric (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    F.periodData.periodTorus → ℝ :=
  Quotient.lift (F.thetaFrameMetricWeight hP U V i)
    (fun v w h => F.thetaFrameMetricWeight_quotient_eq hP U V hdeg i v w (Quotient.sound h))

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaFrameMetric_mk (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (w : F.periodData.space) :
    F.thetaFrameMetric hP U V hdeg i (QuotientAddGroup.mk w) = F.thetaFrameMetricWeight hP U V i w := rfl

end

variable (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP)) (hdeg : V.degree = U.degree + 1)

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaMetricDescent_integral : AlgebraicGeometry.IsIntegral M.abelian.toOver.left :=
  M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaMetricDescent_smooth : AlgebraicGeometry.Smooth M.abelian.toOver.hom :=
  M.abelian.variety.presentation.smooth

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaFrameMetric (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) : ℝ :=
  F.thetaFrameMetric hP U V hdeg i (M.period.symm p)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaFrameMetric_period
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : F.periodData.space) :
    M.nativeThetaFrameMetric U V hdeg i (M.vectorPeriod w) = F.thetaFrameMetricWeight hP U V i w :=
  congrArg (F.thetaFrameMetric hP U V hdeg i) (M.period.symm_apply_apply (QuotientAddGroup.mk w))

end

/-! The descended Gaussian weights are positive on every actual native
theta-frame domain and obey the gluing equation for the actual sheaf
frame units at every complex point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

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

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaMetric_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaMetric_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaFrameOpen_period
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : F.periodData.space) :
    (M.vectorPeriod w).left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈ RepresentationTheory.Theta.Geometric.ProductFrames.thetaQuotientOpen f.left g.left i.1 i.2 ↔
      w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i :=
  and_congr (RepresentationTheory.Theta.Geometric.ProductValues.thetaCoordinateOpen_mem_of_point U f (M.vectorPeriod w) w (hf _) i.1)
    (RepresentationTheory.Theta.Geometric.ProductValues.thetaCoordinateOpen_mem_of_point V g (M.vectorPeriod w) w (hg _) i.2)

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaFrameMetric_positive (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (hp : p.left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈ RepresentationTheory.Theta.Geometric.ProductFrames.thetaQuotientOpen f.left g.left i.1 i.2) :
    0 < M.nativeThetaFrameMetric U V hdeg i p := by
  obtain ⟨t, rfl⟩ := M.period.surjective p
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
  change 0 < M.nativeThetaFrameMetric U V hdeg i (M.vectorPeriod w)
  rw [M.nativeThetaFrameMetric_period]
  exact F.thetaFrameMetricWeight_positive hP U V i w
    ((M.thetaFrameOpen_period U V f g hf hg i w).mp hp)

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaFrameMetric_gluing (hdeg : V.degree = U.degree + 1)
    (i j : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (W : M.abelian.toOver.left.Opens)
    (hi : W ≤ RepresentationTheory.Theta.Geometric.ProductFrames.thetaQuotientOpen f.left g.left i.1 i.2)
    (hj : W ≤ RepresentationTheory.Theta.Geometric.ProductFrames.thetaQuotientOpen f.left g.left j.1 j.2)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (hp : p.left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W) :
    ‖RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue p.left W hp
      (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).sheaf W
        (RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.thetaQuotientIndexedFrame f.left g.left i W hi)
        (RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.thetaQuotientIndexedFrame f.left g.left j W hj) : Γ(M.abelian.toOver.left, W))‖ ^ 2 *
      M.nativeThetaFrameMetric U V hdeg i p = M.nativeThetaFrameMetric U V hdeg j p := by
  obtain ⟨t, rfl⟩ := M.period.surjective p
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
  change _ * M.nativeThetaFrameMetric U V hdeg i (M.vectorPeriod w) =
    M.nativeThetaFrameMetric U V hdeg j (M.vectorPeriod w)
  rw [M.nativeThetaFrameMetric_period, M.nativeThetaFrameMetric_period]
  exact F.thetaFrameMetricWeight_native_transition hP U V f g (M.vectorPeriod w) w
    (hf _) (hg _) i j W hi hj hp ((M.thetaFrameOpen_period U V f g hf hg i w).mp (hi hp))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
