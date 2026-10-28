import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.AmbientTrace
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.CompactDiagram

/-! # Covering Trace -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CoveringTrace.BundleCycles

noncomputable section

/-! A genuine finite complex covering of retained regular supports
compares the independent canonical cycle integrals with its actual
fiber cardinality, for nonprojective smooth ambient schemes as well. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.CompactDiagram.Constructions.Construction
open scoped _root_.Manifold ContDiff

theorem schemeCycle_compact_covering_trace
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (A : IrreducibleCloseds X.left) (p : ℕ)
    (hA : Foundations.Scheme.SupportDimension.supportTranscendenceDimension A X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (B : IrreducibleCloseds Y.left) (q : ℕ)
    (hB : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
    (f : X ⟶ Y)
    (d e : ℕ) {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    [T2Space P] [T2Space Q] [SecondCountableTopology P] [SecondCountableTopology Q]
    [ChartedSpace (Fin d → ℂ) P] [ChartedSpace (Fin e → ℂ) Q]
    [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 P] [IsManifold 𝓘(ℂ, Fin e → ℂ) 1 Q]
    (jA : TopCat.of P ⟶ (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X A p hA).regularAnalyticSpace)
    (jB : TopCat.of Q ⟶ (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion Y B q hB).regularAnalyticSpace)
    (hjA : Topology.IsOpenEmbedding jA) (hjB : Topology.IsOpenEmbedding jB)
    (hlA : IsLocalDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X A) ω jA)
    (hlB : IsLocalDiffeomorph 𝓘(ℂ, Fin e → ℂ) 𝓘(ℂ, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Y B) ω jB)
    (h : TopCat.of P ⟶ TopCat.of Q) (hh : IsProperMap h)
    (hlh : IsLocalDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ω h)
    (hsquare : (jA ≫ CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X A p hA) ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f =
      h ≫ (jB ≫ CompactTrace.BundleCycles.schemeCycleRegularAmbientMap Y B q hB))
    (degree : ℕ) (hdegree : ∀ y : Q, Nat.card (h ⁻¹' {y}) = degree)
    (n : ℕ) (hd : 2 * d = n) (he : 2 * e = n)
    (hTA : CompactTrace.BundleCycles.schemeCycleTraceDegree X A = n) (hTB : CompactTrace.BundleCycles.schemeCycleTraceDegree Y B = n)
    (hp : 2 * p + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
    (hq : 2 * q + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
    (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (hK : IsCompact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))))
    (hLA : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X A)
    (hLB : (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Y B)
    (hRangeA : CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X A p hA ⁻¹'
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))) ⊆ Set.range jA)
    (hRangeB : CompactTrace.BundleCycles.schemeCycleRegularAmbientMap Y B q hB ⁻¹' (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆ Set.range jB)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ n) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (2 * p) n hp (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X A p hA)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)), hK⟩ n
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
          (A := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))ᶜ)
          (B := (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ) (fun _ hx => hx) n b)) =
    (degree : ℚ) • AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (2 * q) n hq (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Y B q hB)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) L n b) := by
  let F := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f
  let K : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)), hK⟩
  let u := jA ≫ CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X A p hA
  let v := jB ≫ CompactTrace.BundleCycles.schemeCycleRegularAmbientMap Y B q hB
  have hsource : IsCompact (u ⁻¹' (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) :=
    AmbientTrace.BundleCycles.schemeCycle_isCompact_openRegularPreimage X A p hA jA hjA K hLA hRangeA
  have htarget : IsCompact (v ⁻¹' (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))) :=
    AmbientTrace.BundleCycles.schemeCycle_isCompact_openRegularPreimage Y B q hB jB hjB L hLB hRangeB
  let fund := CycleClass.Thom.ProperImage.FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree d (u ⁻¹' (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) hsource n hd
  let rU := HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ u
    (A := (u ⁻¹' (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))ᶜ) (B := (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))ᶜ)
    (fun _ hx => hx)) n
  have hs := AmbientTrace.BundleCycles.schemeCycleClass_compactTrace_from_open X A p hA d jA hjA hlA K hLA hRangeA n hd hTA hp
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) F
      (A := (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))ᶜ) (B := (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ) (fun _ hx => hx) n b)
  have hn := CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeHomologyEvaluation_naturality (ModuleCat.of ℚ ℚ) F
    (A := (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))ᶜ) (B := (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ)
    (fun _ hx => hx) n b (rU fund)
  have hc := ConcreteCategory.congr_hom (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ u F
    (A := (u ⁻¹' (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))ᶜ) (B := (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))ᶜ)
    (C := (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ) (fun _ hx => hx) (fun _ hx => hx) n) fund
  have heq := CycleClass.Thom.ProperImage.CompactDiagram.Constructions.Construction.rationalCompactFundamentalClassInDegree_push_congr d (u ≫ F) (h ≫ v)
    hsquare (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) hsource (hh.isCompact_preimage htarget) n hd
  have hcover := CycleClass.Thom.ProperImage.CompactDiagram.Constructions.Construction.rationalCompactFundamentalClassInDegree_comp_degree d e h hh hlh degree hdegree
    v (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) htarget n hd he
  have ht := AmbientTrace.BundleCycles.schemeCycleClass_compactTrace_from_open Y B q hB e jB hjB hlB L hLB hRangeB n he hTB hq b
  have hpush := hc.trans (heq.trans hcover)
  have hev := congrArg (CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ n b) hpush
  exact hs.trans (hn.trans (hev.trans ((map_smul _ _ _).trans (congrArg (fun a => (degree : ℚ) • a) ht.symm))))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CoveringTrace.BundleCycles
