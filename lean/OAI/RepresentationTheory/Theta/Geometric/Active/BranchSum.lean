import OAI.RepresentationTheory.Theta.Geometric.Active.BranchTraceModels
import OAI.RepresentationTheory.Theta.Geometric.AlbaneseBranchPullback
import OAI.RepresentationTheory.Theta.Geometric.Rational.ThetaPullback

/-! # Branch Sum -/

namespace OAI.RepresentationTheory.Theta.Geometric.Active.BranchSum

noncomputable section

/-! An actual rational description of the corrected branch targets
identifies the algebraic theta trace with the original period derivatives. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

namespace ActiveHeckeThetaData

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (hh : D.HasHolomorphicThetaData) (ha : D.HasRationalThetaCovariance)
    (w : Intrinsic.Hecke.ActiveWeight)

local notation "Branches" => D.ClearedBranch (D.totalPeriodMap j X component cover) w
local notation "Lift" => D.thetaAlbaneseLift hg j X component cover hcover hh ha

include hA in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.activeTheta_smooth_branch_sum [Fintype Branches]
    (g : Branches → D.RationalSU)
    (htarget : ∀ b x, D.clearedBranchTarget A.shift b x =
      D.totalPeriodMap j X component cover (D.rationalPeriodPoint (g b) x))
    (φ : D.sphericalInputs) :
    let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
    Projective.FormOnDomain.projectiveFormOnDomain D.domain X cover hc
      (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
        (D.pel.albanesePullback hg
          (D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished w)) (Lift φ)))) =
      ∑ b : Branches, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (D.rationalPeriodPoint (g b))
        (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (D.rationalPeriodPoint_contMDiff (g b)))
        (D.thetaBallSmoothForm hh φ) := by
  obtain ⟨Y, target, l, hl, hpoint, htrace⟩ :=
    D.exists_activeBranchTrace_models hg hgood hIsogenyQuotient A hA j X component cover hcover w
  refine (htrace (Lift φ)).trans ?_
  apply Finset.sum_congr rfl
  intro b _
  exact D.thetaAlbaneseLift_branch_pullback hg j X component cover hcover hh ha
    (Y b) (target b) (l b) (hl b) (D.rationalPeriodPoint (g b))
    (D.rationalPeriodPoint_contMDiff (g b)) (fun x => (hpoint b x).trans (htarget b x)) φ

include hA in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.activeTheta_branch_sum_chart [Fintype Branches]
    (g : Branches → D.RationalSU)
    (htarget : ∀ b x, D.clearedBranchTarget A.shift b x =
      D.totalPeriodMap j X component cover (D.rationalPeriodPoint (g b) x))
    (φ : D.sphericalInputs) (x : D.domain) (u : LinearTheta.BallCoordinates) :
    let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
    Projective.FormOnDomain.periodChartEvaluation D.domain x u
      (Projective.FormOnDomain.projectiveFormOnDomain D.domain X cover hc
        (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
          (D.pel.albanesePullback hg
            (D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished w)) (Lift φ))))) =
      ∑ b : Branches, D.thetaUniversal φ.val (D.periodMap (g b) x.val)
        (fderiv ℂ (D.periodMap (g b)) x.val u) := by
  have h := congrArg (Projective.FormOnDomain.periodChartEvaluation D.domain x u)
    (D.activeTheta_smooth_branch_sum hg hgood hIsogenyQuotient A hA j X component cover hcover hh ha w g htarget φ)
  simpa only [map_sum, D.rationalThetaPullback_chart] using h

end ActiveHeckeThetaData

end

end OAI.RepresentationTheory.Theta.Geometric.Active.BranchSum
