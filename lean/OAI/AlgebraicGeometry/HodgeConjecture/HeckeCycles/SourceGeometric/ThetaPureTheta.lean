import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaPureForms
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaManifoldTheta
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportPeriodForm

/-! # Theta Pure Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaPureTheta.CM

noncomputable section

/-! The canonical algebraic lift has an actual pure closed representative
satisfying the original source theta predicate on the same ball. -/

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
theorem represents (hg : T.pel.HasIntegralModelGeometry)
    (Θ : T.sphericalInputs →ₗ[ℂ] T.pel.OneFormsA)
    (j : Fin T.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ T.componentComplex j) (cover : T.domain → X.analyticSpace)
    (hcover : T.IsPeriodUniformization X cover)
    (hΘ : T.IsCanonicalThetaLift hg j (T.totalPeriodMap j X component cover) Θ)
    (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places)) (hφ : Theta.Weil.CM.finiteWeilInput φ ∈ T.sphericalInputs)
    (hdom : B.domainOpen = T.domain) :
    GeometricSource.CM.RepresentsTheta E L φ X (cover ∘ ReferenceCover.CM.transportPoint hdom)
      (Geometric.ThetaPureForms.CM.representative T hg Θ j X component ⟨Theta.Weil.CM.finiteWeilInput φ, hφ⟩) :=
  TransportPeriodForm.CM.evaluation hdom X cover
    (Geometric.ThetaPureForms.CM.representative T hg Θ j X component ⟨Theta.Weil.CM.finiteWeilInput φ, hφ⟩).val.val.val
    (GeometricSource.CM.thetaOneForm E L φ)
    (ThetaManifoldTheta.CM.pullback E L T hperiod hproject hg Θ j X component cover hcover hΘ φ hφ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaPureTheta.CM
