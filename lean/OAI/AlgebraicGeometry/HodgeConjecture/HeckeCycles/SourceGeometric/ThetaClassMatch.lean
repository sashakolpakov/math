import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaPureTheta
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaReferenceCoverMap
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceThetaClassMatch

/-! # Theta Class Match -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaClassMatch.CM

noncomputable section

/-! The actual reference theta class is the pullback of the canonical
GeometricTheta algebraic theta class along a constructed holomorphic surjection. -/

open scoped Classical _root_.NumberField _root_.Manifold ContDiff TensorProduct
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (T : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K places.count q (GeometricSource.CM.Positions E places) Ga MpR MpF MpA)
  (hperiod : T.period = L.period) (hproject : T.project = Theta.Projection.CM.projection E L)
  (hb : T.pel.reference.b = B.b) (hμ : T.pel.reference.μ = E.val.toRingHom)
  (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice T.pel.reference.lattice)

include hperiod hproject hb hμ in
theorem exists_matching_map (hg : T.pel.HasIntegralModelGeometry) (hc : T.HasFiniteCoordinates)
    (Θ : T.sphericalInputs →ₗ[ℂ] T.pel.OneFormsA)
    (j : Fin T.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ T.componentComplex j) (cover : T.domain → X.analyticSpace)
    (hcover : T.IsPeriodUniformization X cover)
    (hΘ : T.IsCanonicalThetaLift hg j (T.totalPeriodMap j X component cover) Θ)
    (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places)) (hφ : Theta.Weil.CM.finiteWeilInput φ ∈ T.sphericalInputs)
    (Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : (CoverFactor.CM.withLattice E B T.pel.reference.lattice hΛ.1 hΛ.2.1 hΛ.2.2).Domain → Y.analyticSpace)
    (hπ : (CoverFactor.CM.withLattice E B T.pel.reference.lattice hΛ.1 hΛ.2.1 hΛ.2.2).IsBallCover T.pel.level Y π)
    (α : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms Y.analyticModel Y.analyticSpace 1 0)
    (hα : GeometricSource.CM.RepresentsTheta E L φ Y π α)
    (θY : ComplexMultiplication.WeightOne.CM.Complexification (Y.rationalCohomology 1))
    (hθY : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) 1 θY =
      (Y.deRhamBettiIso 1).hom (Y.deRhamClass 1 α.val)) :
    ∃ f : C(Y.analyticSpace, X.analyticSpace),
      ContMDiff 𝓘(ℂ, Y.analyticModel) 𝓘(ℂ, X.analyticModel) ∞ f ∧
      Function.Surjective f ∧
      (AnalyticPullback.CM.pullbackQ f 1).hom.baseChange ℂ
        (Geometric.ThetaPureForms.CM.betti T hg Θ j X component ⟨Theta.Weil.CM.finiteWeilInput φ, hφ⟩) = θY ∧
      ∀ z, f (π z) = Geometric.ThetaReferenceCoverMap.CM.transported E T (CoverFactor.CM.withLattice E B T.pel.reference.lattice hΛ.1 hΛ.2.1 hΛ.2.2) hb hμ cover z := by
  let : FiniteDimensional ℚ (Y.rationalCohomology 1) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_cohomology_finite Y.presentation 1
  obtain ⟨_, f, hf, hsurj, hcomp⟩ :=
    Geometric.ThetaReferenceCoverMap.CM.exists_map E T (CoverFactor.CM.withLattice E B T.pel.reference.lattice hΛ.1 hΛ.2.1 hΛ.2.2) hb hμ rfl hc X Y cover hcover π hπ
  let c := Geometric.ThetaReferenceCoverMap.CM.transported E T (CoverFactor.CM.withLattice E B T.pel.reference.lattice hΛ.1 hΛ.2.1 hΛ.2.2) hb hμ cover
  let ψ : T.sphericalInputs := ⟨Theta.Weil.CM.finiteWeilInput φ, hφ⟩
  let β := Geometric.ThetaPureForms.CM.representative T hg Θ j X component ψ
  have hgeom : ReferenceCover.CM.CoverProperty B.domainOpen Y π :=
    ⟨hπ.2.1, hπ.2.2.1, hπ.2.2.2.1, hπ.2.2.2.2.1⟩
  have hβ : GeometricSource.CM.RepresentsTheta E L φ X c β :=
    ThetaPureTheta.CM.represents E L T hperiod hproject hg Θ j X component cover hcover hΘ φ hφ
      (Geometric.ThetaReferenceCoverMap.CM.domain_eq E T B hb hμ)
  exact ⟨f, hf, hsurj,
    ReferenceThetaClassMatch.CM.classes E L φ Y X π c hgeom f hf hcomp α β hα hβ θY
      (Geometric.ThetaPureForms.CM.betti T hg Θ j X component ψ) hθY
      (Geometric.ThetaPureForms.CM.betti_represents T hg Θ j X component ψ), hcomp⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaClassMatch.CM
