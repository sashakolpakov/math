import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaManifoldPullback
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Projection

/-! # Theta Manifold Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaManifoldTheta.CM

noncomputable section

/-! A canonical algebraic lift with the original source period and
projection pulls back to the original smooth theta derivative. The
constructed source candidate has these two field equalities by definition. -/

open scoped Classical _root_.NumberField _root_.Manifold ContDiff
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (T : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K places.count q (GeometricSource.CM.Positions E places) Ga MpR MpF MpA)
  (hperiod : T.period = L.period) (hproject : T.project = Theta.Projection.CM.projection E L)

include hperiod hproject in
theorem universal (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places)) (z ξ : GeometricSource.CM.BallChart) :
    T.thetaUniversal (Theta.Weil.CM.finiteWeilInput φ) z ξ = GeometricSource.CM.thetaOneForm E L φ z ξ := by
  change RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear T.period T.project (Theta.Weil.CM.finiteWeilInput φ) z ξ = _
  rw [hperiod, hproject]
  exact Theta.Projection.CM.canonical_oneForm_eq_source E L φ z ξ

include hperiod hproject in
theorem pullback (hg : T.pel.HasIntegralModelGeometry)
    (Θ : T.sphericalInputs →ₗ[ℂ] T.pel.OneFormsA)
    (j : Fin T.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ T.componentComplex j)
    (cover : T.domain → X.analyticSpace)
    (hcover : T.IsPeriodUniformization X cover)
    (hΘ : T.IsCanonicalThetaLift hg j (T.totalPeriodMap j X component cover) Θ)
    (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (hφ : Theta.Weil.CM.finiteWeilInput φ ∈ T.sphericalInputs)
    (x : T.domain) (ξ : GeometricSource.CM.BallChart) :
    (CMExtraction.Intrinsic.PeriodForms.thetaOnPeriodVariety T hg Θ j X component ⟨Theta.Weil.CM.finiteWeilInput φ, hφ⟩).val
      (cover x) (fun _ : Fin 1 => mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) cover x ξ) =
        GeometricSource.CM.thetaOneForm E L φ x.val ξ :=
  (Geometric.ThetaManifoldPullback.CM.apply T hg Θ j X component cover hcover hΘ
    ⟨Theta.Weil.CM.finiteWeilInput φ, hφ⟩ x ξ).trans
    (universal E L T hperiod hproject φ x.val ξ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaManifoldTheta.CM
