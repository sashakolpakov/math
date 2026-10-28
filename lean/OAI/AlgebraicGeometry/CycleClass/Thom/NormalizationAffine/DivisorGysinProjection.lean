import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGysin
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraph
import OAI.AlgebraicGeometry.CycleClass.Thom.ProjectedDegree

/-! # Divisor Gysin Projection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGysinProjection.Constructions

noncomputable section

/-! The actual affine divisor Gysin class projects to the original ambient image cycle, with the actual residue degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorRegularImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGraphImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphDimension.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphClosed.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinAmbient.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport OAI.AlgebraicGeometry.CycleClass.Thom.AmbientInverse.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left] [QuasiCompact a.left]
  (g : X ⟶ Y) (j : Y ⟶ V.toOver) [IsOpenImmersion j.left]
  (hs : a ≫ Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W = g ≫ j)
  (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) (hf : Function.Surjective f)
  [IsClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f).left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d))]
  (z : {x : X.left // Order.coheight x = 1})
  (U : Opens V.analyticSpace) (hU : (U : Set V.analyticSpace) ⊆ NormalizationDivisor.GraphOpen.Constructions.goodAmbient V W (Open.PrimeSupport.Constructions.ambientPrime a z))
  (hUJ : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (U : Set V.analyticSpace) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) : ChartedSpace (V.analyticModel × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace V.analyticModel U (Fin d → ℂ) (Fin d → ℂ)
local instance (priority := low) : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance : IsManifold 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold
local instance : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) × (Fin d → ℂ)) ω
    (U × (Fin d → ℂ)) := Product.Immersion.Constructions.productModel_isManifold

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraph.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.LocalGraph.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Image.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProjectedDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

variable (K : Set (Fin d → ℂ)) (hK : IsCompact K)
  (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U →
    Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K)

def affineDivisorProjection :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U × (Fin d → ℂ)))
      (Set.range (EtaleLocalGraph.Constructions.localGraph (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
        (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f)))ᶜ (2 * ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1)) →ₗ[ℚ]
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
        (hU.trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a z)))))ᶜ (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1)) :=
  Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U)
    (Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
      (hU.trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a z))))) K hK
    (Set.range (EtaleLocalGraph.Constructions.localGraph (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f)))
    (NormalizationDivisor.LocalGraph.Constructions.Class.divisorLocalGraph_bound V W (Open.PrimeSupport.Constructions.ambientPrime a z) U hU
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f) K
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates_bound V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f K hb))
    (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1)) (2 * ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1)) (by omega)

variable (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d)))
    (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (Geometric.DimensionCycles.dimensionCodimension V W + d)
      (GraphDimension.Constructions.parentGraph_dimension V W a Y j d)).regularComplementInclusion)ᶜ) (2 * (Geometric.DimensionCycles.dimensionCodimension V W + d)))

variable (hc : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * (Geometric.DimensionCycles.dimensionCodimension V W + d)) c =
  (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (Geometric.DimensionCycles.dimensionCodimension V W + d)
    (GraphDimension.Constructions.parentGraph_dimension V W a Y j d)).regularThomClass)

include hf in
theorem affineDivisorGysin_project_imageCycleClass :
    affineDivisorProjection V W a d f z U hU hcover K hK hb
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ))
        (DivisorGysin.Constructions.divisorPullback_mapsTo V W a g j hs d f z U hU hUJ hcover) (2 * ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1))
        (SchemeDivisor.Gysin.Constructions.divisorGysinClass (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z (Geometric.DimensionCycles.dimensionCodimension V W + d)
          (GraphDimension.Constructions.parentGraph_dimension V W a Y j d) c hc)) =
      ((Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree (Open.PrimeSupport.Constructions.ambientPrime a z).val : ℚ) •
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
          (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_mapsTo (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
            (hU.trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a z)))) (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1))
          (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a z)).rationalSupportedCycleClass := by
  have ht := congrArg (affineDivisorProjection V W a d f z U hU hcover K hK hb)
    (DivisorGysin.Constructions.affineDivisorGysin_eq_coverGraphThom V W a g j hs d f hf z U hU hUJ hcover c hc)
  refine ht.trans ?_
  unfold affineDivisorProjection
  refine (ProjectedDegree.Constructions.projectAt_Thom_codimension d (TopCat.of U)
    (EtaleLocalGraph.Constructions.localGraph (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f))
    (EtaleLocalGraph.Constructions.localGraph_analytic (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f)
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates_analytic V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f))
    (EtaleLocalGraph.Constructions.localGraph_differential_injective (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f)
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates_analytic V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f))
    (NormalizationDivisor.AffineGraphClosed.Constructions.coverAffineGraph_closedEmbedding V W (Open.PrimeSupport.Constructions.ambientPrime a z) a f U hcover hU hf)
    (Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
      (hU.trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a z))))) K hK
    (NormalizationDivisor.LocalGraph.Constructions.Class.divisorLocalGraph_bound V W (Open.PrimeSupport.Constructions.ambientPrime a z) U hU
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f) K
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates_bound V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f K hb))
    (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1)) ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1)
    ((Geometric.DimensionCycles.dimensionCodimension V W + 1) + d) (GraphDimension.Constructions.coverPrimeGraph_codimension V W a d z)
    (NormalizationDivisor.GraphOpen.Constructions.sourceGraph_codimension V W (Open.PrimeSupport.Constructions.ambientPrime a z) d) (by omega) (Nat.mul_add 2 (Geometric.DimensionCycles.dimensionCodimension V W + 1) d).symm).trans ?_
  exact NormalizationDivisor.AffineGraph.Constructions.Class.affineDivisorGraph_project_imageCycleClass V W (Open.PrimeSupport.Constructions.ambientPrime a z) U hU a hcover f hf K hK hb

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGysinProjection.Constructions
