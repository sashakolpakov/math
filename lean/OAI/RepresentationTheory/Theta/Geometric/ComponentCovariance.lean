import OAI.RepresentationTheory.Theta.Geometric.Active.BranchSum
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicSum
import OAI.RepresentationTheory.Theta.Geometric.Period.ChartFaithfulness
import OAI.RepresentationTheory.Theta.Geometric.Period.AlgebraicFaithfulness

/-! # Component Covariance -/

namespace OAI.RepresentationTheory.Theta.Geometric.ComponentCovariance.ActiveHeckeThetaData

noncomputable section

/-! The actual raw Hecke trace of the algebraic theta lift satisfies
finite Weil covariance on the principal component once its rational
branch targets, including the entire away marking, have been identified. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

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
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.activeTheta_covariance_on_component [Fintype Branches]
    (T : SphericalGU.Spherical.SL3Hecke q)
    (hT : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (SphericalGU.Spherical.integralSL3 q) (Intrinsic.Hecke.activeSLRepresentative q w) T)
    (β : Branches ≃ Intrinsic.Hecke.activeCosets q w) (g : Branches → D.RationalSU)
    (hcoset : ∀ b, (QuotientGroup.mk (D.activeLocal (g b))⁻¹ :
      SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) = (β b).val)
    (haway : ∀ b, D.away (g b) ∈ D.awayLevel)
    (htarget : ∀ b x, D.clearedBranchTarget A.shift b x =
      D.totalPeriodMap j X component cover (D.rationalPeriodPoint (g b) x))
    (φ : D.sphericalInputs) :
    let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
    Projective.FormOnDomain.projectiveFormOnDomain D.domain X cover hc
      (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
        (D.pel.albanesePullback hg
          (D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished w)) (Lift φ)))) =
      D.thetaBallSmoothForm hh (D.sphericalWeil T φ) := by
  apply Period.ChartFaithfulness.smoothForm_eq_of_periodChartEvaluation
  intro x u
  refine (D.activeTheta_branch_sum_chart hg hgood hIsogenyQuotient A hA j X component cover hcover hh ha
    w g htarget φ x u).trans ?_
  rw [Rational.ThetaPullback.periodChartEvaluation_apply, D.thetaBallSmoothForm_apply]
  exact D.native_raw_theta_sum ha w T hT β g hcoset haway φ x u

include hA in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.activeTheta_algebraic_component_covariance [Fintype Branches]
    (T : SphericalGU.Spherical.SL3Hecke q)
    (hT : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (SphericalGU.Spherical.integralSL3 q) (Intrinsic.Hecke.activeSLRepresentative q w) T)
    (β : Branches ≃ Intrinsic.Hecke.activeCosets q w) (g : Branches → D.RationalSU)
    (hcoset : ∀ b, (QuotientGroup.mk (D.activeLocal (g b))⁻¹ :
      SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) = (β b).val)
    (haway : ∀ b, D.away (g b) ∈ D.awayLevel)
    (htarget : ∀ b x, D.clearedBranchTarget A.shift b x =
      D.totalPeriodMap j X component cover (D.rationalPeriodPoint (g b) x))
    (φ : D.sphericalInputs) :
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
      (D.pel.albanesePullback hg
        (D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished w)) (Lift φ))) =
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
      (D.pel.albanesePullback hg (Lift (D.sphericalWeil T φ))) := by
  apply D.periodUniformization_forms_injective X cover hcover
  exact (D.activeTheta_covariance_on_component hg hgood hIsogenyQuotient A hA j X component cover hcover hh ha
    w T hT β g hcoset haway htarget φ).trans
    (D.thetaAlbaneseLift_domain_pullback hg j X component cover hcover hh ha (D.sphericalWeil T φ)).symm

end

end OAI.RepresentationTheory.Theta.Geometric.ComponentCovariance.ActiveHeckeThetaData
