import OAI.RepresentationTheory.Theta.Geometric.AlbaneseLift
import OAI.RepresentationTheory.Theta.Geometric.CanonicalPeriodGerms
import OAI.RepresentationTheory.Theta.Geometric.PeriodClosed
import OAI.RepresentationTheory.Theta.Geometric.CanonicalUniqueness

/-! # Canonical Existence -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Existence and uniqueness of the actual canonical algebraic theta lift,
including its equality on every permitted period germ and zero extension. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open Filter
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (hh : D.HasHolomorphicThetaData) (ha : D.HasRationalThetaCovariance)

theorem Data.ActiveHeckeThetaData.thetaAlbaneseLift_isCanonical :
    D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover)
      (D.thetaAlbaneseLift hg j X component cover hcover hh ha) := by
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : X.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated X
  let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable
    hcover.2.2.1
  let Θ := D.thetaAlbaneseLift hg j X component cover hcover hh ha
  let m := component.hom ≫ D.componentComplexInclusion j
  have hlocal (x : D.domain) : ∃ p,
      D.IsPeriodChartAt (D.totalPeriodMap j X component cover) x p ∧
      ∀ φ : D.sphericalInputs,
        DifferentialNaturality.formInPeriodCoordinates x.val p (D.pel.albanesePullback hg (Θ φ)) =
          D.thetaUniversal φ.val x.val := by
    obtain ⟨U, hU, a, haU⟩ := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift X.toOver (cover x)
    have hxU : cover x ∈ AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X.toOver U := by
      change cover x ∈ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (U : Set X.toOver.left)
      rw [← AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap X.toOver U hU]
      exact ⟨a, haU⟩
    let y : AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodCharts.periodNeighborhood X.toOver U D.domain cover hc := ⟨x, hxU⟩
    let p := AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodCharts.localPeriodTest X.toOver U hU D.domain cover hc y
    refine ⟨p ≫ m, ?_, ?_⟩
    · have h := AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodCharts.localPeriodTest_germ X.toOver U hU D.domain cover hc y
      filter_upwards [h] with z hz
      intro hzD
      exact (Category.assoc _ p m).symm.trans (congrArg (· ≫ m) (hz hzD))
    · intro φ
      ext u
      have hs : AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm X.toOver
          (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback m (D.pel.albanesePullback hg (Θ φ))) =
          D.periodThetaSmoothForm X cover hcover hh ha φ :=
        congrArg Subtype.val (D.thetaAlbaneseLift_closed_pullback hg j X component cover hcover hh ha φ)
      have h := AlgebraicGeometry.HodgeConjecture.CMExtraction.GlobalPeriodComparison.globalPeriodTest_pullback X.toOver U hU D.domain cover hc y
        (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback m (D.pel.albanesePullback hg (Θ φ))) u
      rw [hs] at h
      have hpull := congrArg (fun F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm LinearTheta.BallCoordinates D.domain 1 =>
        F.val.inChart (chartAt LinearTheta.BallCoordinates x) x.val (fun _ => u))
        (D.periodThetaSmoothForm_pullback X cover hcover hh ha φ)
      exact h.symm.trans (hpull.trans (D.thetaBallSmoothForm_chart hh φ x u))
  refine ⟨fun x => ⟨(hlocal x).choose, (hlocal x).choose_spec.1⟩, ?_, ?_⟩
  · intro φ x p hp
    obtain ⟨t, ht, hθ⟩ := hlocal x
    exact (D.canonicalPeriodChart_form_eq hg _ x p t hp ht (Θ φ)).trans (hθ φ)
  · intro i hij φ
    exact D.thetaAlbaneseLift_complement hg j X component cover hcover hh ha i hij φ

include hcover hh ha in
theorem Data.ActiveHeckeThetaData.existsUnique_canonicalThetaLift :
    ∃ Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Θ ∧
      ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
        D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Ψ → Ψ = Θ := by
  let Θ := D.thetaAlbaneseLift hg j X component cover hcover hh ha
  have hΘ := D.thetaAlbaneseLift_isCanonical hg j X component cover hcover hh ha
  exact ⟨Θ, hΘ, fun Ψ hΨ => D.canonicalThetaLift_unique hg j X component cover hcover Θ Ψ hΘ hΨ⟩

end

end OAI.RepresentationTheory.Theta.Geometric
