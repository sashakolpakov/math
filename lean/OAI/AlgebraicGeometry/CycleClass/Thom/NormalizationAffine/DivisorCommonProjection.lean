import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphBaseRange
import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.BothSupportEnlargement

/-! # Divisor Common Projection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorCommonProjection.Constructions

noncomputable section

/-! Each actual normalized divisor graph projects into a common supported group; its image support is derived from the actual cover and bounded intersection graph. -/

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
  (U : Opens V.analyticSpace)
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

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialNormalizationGraph.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Open.AmbientImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorComplement.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionPullback.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphClasses.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphProjection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGysinProjection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphBaseRange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.BothSupportEnlargement.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.LocalGraph.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Image.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

variable {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d))
  (R : X.left.Opens) (z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R)
  (hR : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ⁻¹' (Set.range v)ᶜ ⊆
    (Scheme.SectionEvaluation.Constructions.analyticOpen X R : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
  (hU : (U : Set V.analyticSpace) ⊆ NormalizationDivisor.GraphOpen.Constructions.goodAmbient V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))

include hs hR hU in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem divisorGraph_le_intersection :
    Set.range (EtaleLocalGraph.Constructions.localGraph (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))
      (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩) U a hcover f)) ⊆
    Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f) ∩
      Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v) := by
  intro y hy
  by_contra hn
  exact IntersectionSupport.Constructions.intersectionDivisor_mapsTo V W a g j hs d f U hUJ hcover v R z hR hU hn hy

variable (S : Set U) (K : Set (Fin d → ℂ)) (hK : IsCompact K)
  (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U →
    Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K)
  (hT : Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f) ∩
    Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v) ⊆ S ×ˢ K)

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
include hs hR hT hcover in
theorem divisorImage_le_commonSupport :
    Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
      (hU.trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))) ⊆ S :=
  NormalizationDivisor.GraphBaseRange.Constructions.imageCycleSupport_le_of_graph_bound V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩) U hU
    (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩) U a hcover f) S K
    ((divisorGraph_le_intersection V W a g j hs d f U hUJ hcover v R z hR hU).trans hT)

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
include hb in
theorem divisorGraphThom_project_commonSupport :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) S K hK
      (Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f) ∩
        Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v)) hT
      (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1)) (2 * ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1)) (by omega)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (U × (Fin d → ℂ))))
        (IntersectionSupport.Constructions.intersectionDivisor_mapsTo V W a g j hs d f U hUJ hcover v R z hR hU)
        (2 * ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1))
        (GraphClasses.Constructions.divisorGraphThomClass V W a d f hf ⟨z.val, z.property.1⟩ U hU hcover)) =
    ((Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ) •
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
        (A := Sᶜ)
        (B := (Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
          (hU.trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))))ᶜ)
        (fun _ hx hy => hx (divisorImage_le_commonSupport V W a g j hs d f U hUJ hcover v R z hR hU S K hT hy))
        (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1))
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
          (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_mapsTo (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
            (hU.trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))))
          (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1))
          (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)).rationalSupportedCycleClass) := by
  have h := Projection.BothSupportEnlargement.Constructions.projectAt_support_enlargement d (TopCat.of U)
    (Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
      (hU.trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))))) S
    (divisorImage_le_commonSupport V W a g j hs d f U hUJ hcover v R z hR hU S K hT) K hK
    (Set.range (EtaleLocalGraph.Constructions.localGraph (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))
      (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩) U a hcover f)))
    (Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f) ∩
      Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v))
    (NormalizationDivisor.LocalGraph.Constructions.Class.divisorLocalGraph_bound V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩) U hU
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩) U a hcover f) K
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates_bound V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩) U a hcover f K hb)) hT
    (divisorGraph_le_intersection V W a g j hs d f U hUJ hcover v R z hR hU)
    (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1)) (2 * ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1)) (by omega)
    (GraphClasses.Constructions.divisorGraphThomClass V W a d f hf ⟨z.val, z.property.1⟩ U hU hcover)
  refine h.trans ?_
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U)) _ _
    (DivisorGysinProjection.Constructions.affineDivisorProjection V W a d f ⟨z.val, z.property.1⟩ U hU hcover K hK hb
      (GraphClasses.Constructions.divisorGraphThomClass V W a d f hf ⟨z.val, z.property.1⟩ U hU hcover)) = _
  rw [GraphProjection.Constructions.divisorGraphThomClass_project_imageCycleClass V W a d f hf ⟨z.val, z.property.1⟩ U hU hcover K hK hb, map_smul]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorCommonProjection.Constructions
