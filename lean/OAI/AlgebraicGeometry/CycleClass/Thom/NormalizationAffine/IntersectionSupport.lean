import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorComplement
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.AmbientImage
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionPullback
import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo

/-! # Intersection Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionSupport.Constructions

noncomputable section

/-! Every constructed normalized divisor graph lies in the actual parent graph intersected with the actual pulled-back equation support. -/

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

abbrev coordinateMap := Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ)

include hs in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [QuasiCompact a.left] in
theorem parentGraph_mapsTo : Set.MapsTo (coordinateMap V j d U hUJ)
    (Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f))ᶜ
    (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (Geometric.DimensionCycles.dimensionCodimension V W + d)
      (GraphDimension.Constructions.parentGraph_dimension V W a Y j d)).regularComplementInclusion)ᶜ :=
  Open.AmbientImage.Constructions.imageTransportMapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f))
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ω) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U)
    (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ) (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f)
    (Normalization.ParentGraphImage.Constructions.parentGraph_image V W a g j hs d f U hUJ)

variable {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d))
  (R : X.left.Opens) (z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R)
  (hR : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ⁻¹' (Set.range v)ᶜ ⊆
    (Scheme.SectionEvaluation.Constructions.analyticOpen X R : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
  (hU : (U : Set V.analyticSpace) ⊆ NormalizationDivisor.GraphOpen.Constructions.goodAmbient V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
include hs hR hU in
theorem intersectionDivisor_mapsTo : Set.MapsTo (𝟙 (TopCat.of (U × (Fin d → ℂ))))
    (Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f) ∩
      Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (coordinateMap V j d U hUJ) v))ᶜ
    (Set.range (EtaleLocalGraph.Constructions.localGraph (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))
      (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩) U a hcover f)))ᶜ := by
  intro y hy
  apply (Set.ext_iff.mp (DivisorComplement.Constructions.affineDivisorGraph_complement V W a g j hs d f ⟨z.val, z.property.1⟩ U hU hUJ hcover) y).mp
  exact SchemeDivisor.IntersectionPullback.Constructions.pullbackDivisor_mapsTo (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (Geometric.DimensionCycles.dimensionCodimension V W + d)
    (GraphDimension.Constructions.parentGraph_dimension V W a Y j d) v
    (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f) (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (coordinateMap V j d U hUJ) v)
    (coordinateMap V j d U hUJ) (parentGraph_mapsTo V W a g j hs d f U hUJ)
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (coordinateMap V j d U hUJ) v) R z hR hy

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionSupport.Constructions
