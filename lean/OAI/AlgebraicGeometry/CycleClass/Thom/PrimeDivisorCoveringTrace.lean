import OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorAmbientTrace
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.CompactDiagram

/-! # Prime Divisor Covering Trace -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorCoveringTrace

noncomputable section

/-! A finite complex covering of retained smooth supports compares a
noncompact source divisor's actual integral with the target geometric cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Trace.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorImmersion.Constructions
  PrimeDivisorAmbientTrace.Constructions.Compact ProperImage.CompactDiagram.Constructions.Construction

theorem divisor_compact_covering_trace
    {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (z : {x : X.left // Order.coheight x = 1})
    {Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {q : ℕ} (T : Geometric.DimensionCycles.DimensionCycleSupport Y q)
    (f : X ⟶ Y.toOver)
    (d e : ℕ) {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    [T2Space P] [T2Space Q] [SecondCountableTopology P] [SecondCountableTopology Q]
    [ChartedSpace (Fin d → ℂ) P] [ChartedSpace (Fin e → ℂ) Q]
    [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 P] [IsManifold 𝓘(ℂ, Fin e → ℂ) 1 Q]
    (jZ : TopCat.of P ⟶ (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularAnalyticSpace)
    (jT : TopCat.of Q ⟶ TopCat.of T.regularAnalyticSpace)
    (hjZ : Topology.IsOpenEmbedding jZ) (hjT : Topology.IsOpenEmbedding jT)
    (hlZ : IsLocalDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularAnalyticModel) ω jZ)
    (hlT : IsLocalDiffeomorph 𝓘(ℂ, Fin e → ℂ) 𝓘(ℂ, T.regularAnalyticModel) ω jT)
    (h : TopCat.of P ⟶ TopCat.of Q) (hh : IsProperMap h)
    (hlh : IsLocalDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ω h)
    (hsquare : (jZ ≫ PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z) ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f =
      h ≫ (jT ≫ ProperImage.Projection.Constructions.Construction.regularAmbientMap T))
    (degree : ℕ) (hdegree : ∀ y : Q, Nat.card (h ⁻¹' {y}) = degree)
    (n : ℕ) (hd : 2 * d = n) (he : 2 * e = n)
    (hZ : PrimeDivisorCompactTrace.Constructions.divisorDegree X z = n) (hT : 2 * T.regularComplexDimension = n)
    (hp : 2 + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
    (hq : (q + q) + n = 2 * Y.complexDimension)
    (L : Compacts Y.analyticSpace) (hK : IsCompact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set Y.analyticSpace)))
    (hLZ : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set Y.analyticSpace) ⊆ Scheme.RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z))
    (hLT : (L : Set Y.analyticSpace) ⊆ T.regularAmbientOpen)
    (hRangeZ : PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹'
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set Y.analyticSpace)) ⊆ Set.range jZ)
    (hRangeT : ProperImage.Projection.Constructions.Construction.regularAmbientMap T ⁻¹' (L : Set Y.analyticSpace) ⊆ Set.range jT)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Y.analyticSpace)
      (L : Set Y.analyticSpace)ᶜ n) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) 2 n hp (SchemeDivisor.Trace.Constructions.Class.absoluteDivisorClass X z)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set Y.analyticSpace), hK⟩ n
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
          (A := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set Y.analyticSpace))ᶜ)
          (B := (L : Set Y.analyticSpace)ᶜ) (fun _ hx => hx) n b)) =
    (degree : ℚ) • Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of Y.analyticSpace)
      (L : Set Y.analyticSpace)ᶜ n b
      (HomologicalComplex.homologyMap
        (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of Y.analyticSpace) (L : Set Y.analyticSpace)ᶜ) n
        ((Y.poincareDuality (q + q) n hq).hom T.geometricCycleClass)) := by
  let F := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f
  let K : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set Y.analyticSpace), hK⟩
  let u := jZ ≫ PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z
  let v := jT ≫ ProperImage.Projection.Constructions.Construction.regularAmbientMap T
  have hsource : IsCompact (u ⁻¹' (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) :=
    PrimeDivisorAmbientTrace.Constructions.Compact.isCompact_openRegularPreimage X z jZ hjZ K hLZ hRangeZ
  have htarget : IsCompact (v ⁻¹' (L : Set Y.analyticSpace)) :=
    ProperImage.CompactDiagram.Constructions.Construction.isCompact_openRegularPreimage T jT hjT L hLT hRangeT
  let fund := ProperImage.FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree d (u ⁻¹' (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) hsource n hd
  let rU := HomologicalComplex.homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ u
    (A := (u ⁻¹' (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))ᶜ) (B := (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))ᶜ)
    (fun _ hx => hx)) n
  have hs := PrimeDivisorAmbientTrace.Constructions.Compact.absoluteDivisorClass_compactTrace_from_open X z d jZ hjZ hlZ K hLZ hRangeZ n hd hZ hp
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) F
      (A := (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))ᶜ) (B := (L : Set Y.analyticSpace)ᶜ) (fun _ hx => hx) n b)
  have hn := Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeHomologyEvaluation_naturality (ModuleCat.of ℚ ℚ) F
    (A := (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))ᶜ) (B := (L : Set Y.analyticSpace)ᶜ)
    (fun _ hx => hx) n b (rU fund)
  have hc := ConcreteCategory.congr_hom (Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ u F
    (A := (u ⁻¹' (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))ᶜ) (B := (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))ᶜ)
    (C := (L : Set Y.analyticSpace)ᶜ) (fun _ hx => hx) (fun _ hx => hx) n) fund
  have heq := ProperImage.CompactDiagram.Constructions.Construction.rationalCompactFundamentalClassInDegree_push_congr d (u ≫ F) (h ≫ v)
    hsquare (L : Set Y.analyticSpace) hsource (hh.isCompact_preimage htarget) n hd
  have hcover := ProperImage.CompactDiagram.Constructions.Construction.rationalCompactFundamentalClassInDegree_comp_degree d e h hh hlh degree hdegree
    v (L : Set Y.analyticSpace) htarget n hd he
  have ht := ProperImage.CompactDiagram.Constructions.Construction.poincareCycleClass_projection_from_open T e jT hjT hlT L hLT hRangeT n he hT hq
  have hpush := hc.trans (heq.trans (hcover.trans (congrArg (fun a => (degree : ℚ) • a) ht.symm)))
  exact hs.trans (hn.trans ((congrArg
    (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of Y.analyticSpace) (L : Set Y.analyticSpace)ᶜ n b) hpush).trans
      (map_smul _ _ _)))

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorCoveringTrace
