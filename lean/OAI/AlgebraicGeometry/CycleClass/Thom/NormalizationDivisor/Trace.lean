import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Range

/-! # Trace -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Trace

noncomputable section

/-! Actual finite normalization sends each canonical divisor integral to
the independent ambient geometric cycle trace with its residue-field degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
  Open.Constructions.Map Open.Constructions.Etale Open.Constructions.Regular
  Analytic.Constructions Boundary.Constructions Boundary.Constructions.CompactSupport
  Range.Constructions.RegularRange SchemeDivisor.Trace.Constructions.Class PrimeDivisorImmersion.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)) := Normalization.AmbientTopology.Constructions.smoothNormalization_metrizable V W
local instance : LocallyOfFiniteType V.toOver.hom := inferInstanceAs (LocallyOfFiniteType V.structureMap)

theorem normalization_divisor_compactTrace
    (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})
    (n : ℕ) (hp : 2 + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom)
    (hq : (Geometric.DimensionCycles.dimensionCodimension V W + 1) + (Geometric.DimensionCycles.dimensionCodimension V W + 1) + n = 2 * V.complexDimension)
    (L : Compacts V.analyticSpace)
    (hLO : (L : Set V.analyticSpace) ⊆ ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen V.toOver (Normalization.AmbientMap.Constructions.ambientOpen V W))
    (hLB : (L : Set V.analyticSpace) ⊆ ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (Boundary.Constructions.omittedBoundary V W z))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ n) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)) 2 n hp
      (SchemeDivisor.Trace.Constructions.Class.absoluteDivisorClass (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)))
        ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (L : Set V.analyticSpace), Boundary.Constructions.CompactSupport.fullAmbientMap_compactPreimage V W L hLO⟩ n
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W))
          (A := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (L : Set V.analyticSpace))ᶜ)
          (B := (L : Set V.analyticSpace)ᶜ) (fun _ hx => hx) n b)) =
    ((Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree z.val : ℚ) •
      Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ n b
        (HomologicalComplex.homologyMap
          (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ) n
          ((V.poincareDuality ((Geometric.DimensionCycles.dimensionCodimension V W + 1) + (Geometric.DimensionCycles.dimensionCodimension V W + 1)) n hq).hom
            (Image.Constructions.imageCycleSupport V W z).geometricCycleClass)) := by
  let S := Normalization.AmbientMap.Constructions.smoothNormalizationOver V W
  change 2 + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom at hp
  let T := Image.Constructions.imageCycleSupport V W z
  let d := Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Open.Constructions.Etale.sourceOpen V W z).hom
  let e := Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Open.Constructions.Etale.targetOpen V W z).hom
  let jZ : TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Open.Constructions.Etale.sourceOpen V W z)) ⟶ (PrimeDivisorImmersion.Constructions.primeDivisorImmersion S z).regularAnalyticSpace :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (Open.Constructions.Regular.sourceToRegular V W z)
  let jT : TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Open.Constructions.Etale.targetOpen V W z)) ⟶ TopCat.of T.regularAnalyticSpace :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (Open.Constructions.Regular.targetToRegular V W z)
  have hZ : PrimeDivisorCompactTrace.Constructions.divisorDegree S z = n := by
    have h := PrimeDivisorTrace.Constructions.primeDivisor_trace_degree S z
    change 2 + PrimeDivisorCompactTrace.Constructions.divisorDegree S z = _ at h
    omega
  have hT : 2 * T.regularComplexDimension = n := by
    have h := T.regularGeometricTrace_degree
    omega
  have hd : 2 * d = n := (congrArg (fun k => 2 * k) (Analytic.Constructions.sourceOpen_dimension V W z)).trans hZ
  have he : 2 * e = n := (congrArg (fun k => 2 * k) (Analytic.Constructions.targetOpen_dimension V W z)).trans hT
  have hsquare : (jZ ≫ PrimeDivisorCompactTrace.Constructions.regularAmbientMap S z) ≫
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) =
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (Open.Constructions.Etale.coverMap V W z) ≫ (jT ≫ ProperImage.Projection.Constructions.Construction.regularAmbientMap T) := by
    ext x
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
        (Scheme.RegularSupport.Constructions.regularToAmbient (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W)
          (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Regular.sourceToRegular V W z) x)) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
        (Scheme.RegularSupport.Constructions.regularToAmbient V.toOver (Image.Constructions.imageSupport V W z))
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Regular.targetToRegular V W z) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Etale.coverMap V W z) x))
    have h := congrArg (fun f : Open.Constructions.Etale.sourceOpen V W z ⟶ V.toOver => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x)
      (Open.Constructions.Regular.regularCover_ambient_square V W z)
    simpa only [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp] using h
  exact PrimeDivisorCoveringTrace.Constructions.divisor_compact_covering_trace z T (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) d e jZ jT
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (Open.Constructions.Regular.sourceToRegular V W z))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (Open.Constructions.Regular.targetToRegular V W z))
    (ProperImage.Open.Constructions.Construction.isLocalDiffeomorph_nativeScheme_openImmersion (Open.Constructions.Regular.sourceToRegular V W z))
    (ProperImage.Open.Constructions.Construction.isLocalDiffeomorph_nativeScheme_openImmersion (Open.Constructions.Regular.targetToRegular V W z))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (Open.Constructions.Etale.coverMap V W z)) (Open.Constructions.Etale.coverMap_analytic_proper V W z)
    (Analytic.Constructions.cover_localDiffeomorph V W z) hsquare ((Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree z.val)
    (Analytic.Constructions.cover_fiber_degree V W z) n hd he hZ hT hp hq L (Boundary.Constructions.CompactSupport.fullAmbientMap_compactPreimage V W L hLO)
    ((Boundary.Constructions.CompactSupport.boundaryComplement_preimage_subset_sourceRegular V W z).trans' (Set.preimage_mono hLB))
    (hLB.trans (Boundary.Constructions.CompactSupport.boundaryComplement_subset_targetRegular V W z))
    (Range.Constructions.RegularRange.sourceRegularPreimage_subset_cover_range V W z (L : Set V.analyticSpace) hLB)
    (Range.Constructions.RegularRange.targetRegularPreimage_subset_cover_range V W z (L : Set V.analyticSpace) hLB) b

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Trace
