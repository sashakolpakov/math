import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Range
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CoveringTrace

/-! # Cycle Trace -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.CycleTrace.BundleCycles

noncomputable section

/-! A finite scheme map transports the canonical cycle integral with
the exact algebraic residue degree on every retained compact test. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open scoped _root_.Manifold ContDiff

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (f : X ⟶ Y) [IsFinite f.left] (Z : IrreducibleCloseds X.left)

local instance : SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
  let : QuasiCompact X.hom := inferInstance
  exact ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_secondCountable X

local instance : SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) := by
  let : QuasiCompact Y.hom := inferInstance
  exact ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_secondCountable Y

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem finiteSupport_compactPreimage (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) :
    IsCompact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))) :=
  (CycleClass.Thom.Integral.SchemeProper.Constructions.isProperMap_integral f).isCompact_preimage L.isCompact

theorem finiteSupport_cycle_compactTrace
    (p q : ℕ)
    (hZ : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (hB : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
    (n : ℕ) (hp : 2 * p + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
    (hq : 2 * q + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
    (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (hL : (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆ Cover.BundleCycles.finiteSupportRetainedOpen f Z)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ n) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (2 * p) n hp (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X Z p hZ)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)), finiteSupport_compactPreimage f L⟩ n
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
          (A := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))ᶜ)
          (B := (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ) (fun _ hx => hx) n b)) =
    (f.left.residueDegree (irreducibleSetEquivPoints Z) : ℚ) •
      AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
        (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (2 * q) n hq (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) q hB)
        (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) L n b) := by
  let d := Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Cover.BundleCycles.finiteSupportSourceOver f Z).hom
  let e := Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Cover.BundleCycles.finiteSupportTargetOver f Z).hom
  let jA : TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Cover.BundleCycles.finiteSupportSourceOver f Z)) ⟶
      (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hZ).regularAnalyticSpace :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (Cover.BundleCycles.finiteSupportSourceToRegular f Z)
  let jB : TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Cover.BundleCycles.finiteSupportTargetOver f Z)) ⟶
      (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) q hB).regularAnalyticSpace :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (Cover.BundleCycles.finiteSupportTargetToRegular f Z)
  have hTA : SchemeCycle.CompactTrace.BundleCycles.schemeCycleTraceDegree X Z = n := by
    have h := SchemeCycle.FundamentalTrace.BundleCycles.schemeCycle_trace_degree X Z p hZ
    change 2 * p + SchemeCycle.CompactTrace.BundleCycles.schemeCycleTraceDegree X Z = _ at h
    omega
  have hTB : SchemeCycle.CompactTrace.BundleCycles.schemeCycleTraceDegree Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) = n := by
    have h := SchemeCycle.FundamentalTrace.BundleCycles.schemeCycle_trace_degree Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) q hB
    change 2 * q + SchemeCycle.CompactTrace.BundleCycles.schemeCycleTraceDegree Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) = _ at h
    omega
  have hd : 2 * d = n := (congrArg (fun k => 2 * k) (Cover.BundleCycles.finiteSupportSourceOver_dimension f Z)).trans hTA
  have he : 2 * e = n := (congrArg (fun k => 2 * k) (Cover.BundleCycles.finiteSupportTargetOver_dimension f Z)).trans hTB
  have hsquare : (jA ≫ SchemeCycle.CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hZ) ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (Cover.BundleCycles.finiteSupportCoverMap f Z) ≫
        (jB ≫ SchemeCycle.CompactTrace.BundleCycles.schemeCycleRegularAmbientMap Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) q hB) := by
    ext x
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportSourceToRegular f Z) x)) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z))
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportTargetToRegular f Z)
          (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportCoverMap f Z) x))
    have h := congrArg (fun k : Cover.BundleCycles.finiteSupportSourceOver f Z ⟶ Y => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k x)
      (Cover.BundleCycles.finiteSupportRegularCover_ambient_square f Z)
    simpa only [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp] using h
  exact SchemeCycle.CoveringTrace.BundleCycles.schemeCycle_compact_covering_trace Z p hZ (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) q hB f d e jA jB
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (Cover.BundleCycles.finiteSupportSourceToRegular f Z))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (Cover.BundleCycles.finiteSupportTargetToRegular f Z))
    (CycleClass.Thom.ProperImage.Open.Constructions.Construction.isLocalDiffeomorph_nativeScheme_openImmersion (Cover.BundleCycles.finiteSupportSourceToRegular f Z))
    (CycleClass.Thom.ProperImage.Open.Constructions.Construction.isLocalDiffeomorph_nativeScheme_openImmersion (Cover.BundleCycles.finiteSupportTargetToRegular f Z))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (Cover.BundleCycles.finiteSupportCoverMap f Z)) (Cover.BundleCycles.finiteSupportCoverMap_analytic_proper f Z)
    (Cover.BundleCycles.finiteSupportCover_localDiffeomorph f Z) hsquare (f.left.residueDegree (irreducibleSetEquivPoints Z))
    (Cover.BundleCycles.finiteSupportCover_fiber_degree f Z) n hd he hTA hTB hp hq L (finiteSupport_compactPreimage f L)
    ((Set.preimage_mono hL).trans (Cover.BundleCycles.finiteSupportRetainedOpen_source_regular f Z))
    (hL.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular f Z))
    (Range.BundleCycles.finiteSupportSourceRegular_range f Z _ hL) (Range.BundleCycles.finiteSupportTargetRegular_range f Z _ hL) b

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.CycleTrace.BundleCycles
