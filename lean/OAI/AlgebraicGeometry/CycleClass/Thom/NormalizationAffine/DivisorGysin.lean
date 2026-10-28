import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGraphImage
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphClosed
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinAmbient

/-! # Divisor Gysin -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGysin.Constructions

noncomputable section

/-! The actual affine-source divisor Gysin class becomes the constructed normalization divisor graph Thom class in the actual graph product coordinates. All image, regularity, immersion, and codimension identifications are proved from the geometric construction. -/

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

include hs hU in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem divisorPullback_mapsTo : Set.MapsTo
    (Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ))
    (Set.range (EtaleLocalGraph.Constructions.localGraph (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f)))ᶜ
    (SchemeDivisor.Gysin.Constructions.divisorImageOpen (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d))) := by
  let Z := SchemeDivisor.OpenImmersion.Constructions.divisorOpenImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z (Geometric.DimensionCycles.dimensionCodimension V W + d)
    (GraphDimension.Constructions.parentGraph_dimension V W a Y j d) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U)
    (DivisorRegularImage.Constructions.affineDivisorGraph_regularImage V W a g j hs d f z U hU)
  intro y hy
  exact SchemeDivisor.OpenImmersion.Constructions.divisorOpenImmersion_mapsTo (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z (Geometric.DimensionCycles.dimensionCodimension V W + d)
    (GraphDimension.Constructions.parentGraph_dimension V W a Y j d) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U)
    (DivisorRegularImage.Constructions.affineDivisorGraph_regularImage V W a g j hs d f z U hU)
    (AmbientInverse.Constructions.ambientInverseMapsTo Z.regularComplementInclusion (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ)
      (ImageInvariant.Constructions.RawThom.imageMapsTo
        (EtaleLocalGraph.Constructions.localGraph (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
          (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f))
        (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ ∘ Z.regularComplementInclusion)
        (DivisorGraphImage.Constructions.affineDivisorImmersion_eq_coverGraph_image V W a g j hs d f z (Geometric.DimensionCycles.dimensionCodimension V W + d)
          (GraphDimension.Constructions.parentGraph_dimension V W a Y j d) U hU hUJ hcover) hy))

variable (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d)))
    (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (Geometric.DimensionCycles.dimensionCodimension V W + d)
      (GraphDimension.Constructions.parentGraph_dimension V W a Y j d)).regularComplementInclusion)ᶜ) (2 * (Geometric.DimensionCycles.dimensionCodimension V W + d)))

variable (hc : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * (Geometric.DimensionCycles.dimensionCodimension V W + d)) c =
  (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (Geometric.DimensionCycles.dimensionCodimension V W + d)
    (GraphDimension.Constructions.parentGraph_dimension V W a Y j d)).regularThomClass)

theorem affineDivisorGysin_eq_coverGraphThom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ))
      (divisorPullback_mapsTo V W a g j hs d f z U hU hUJ hcover) (2 * ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1))
      (SchemeDivisor.Gysin.Constructions.divisorGysinClass (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z (Geometric.DimensionCycles.dimensionCodimension V W + d)
        (GraphDimension.Constructions.parentGraph_dimension V W a Y j d) c hc) =
      Degree.Constructions.ThomClass.complexThomClassInDegree
        (EtaleLocalGraph.Constructions.localGraph (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
          (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f))
        (EtaleLocalGraph.Constructions.localGraph_analytic (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
          (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f)
          (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates_analytic V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f))
        (EtaleLocalGraph.Constructions.localGraph_differential_injective (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
          (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f)
          (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates_analytic V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f))
        (NormalizationDivisor.AffineGraphClosed.Constructions.coverAffineGraph_closedEmbedding V W (Open.PrimeSupport.Constructions.ambientPrime a z) a f U hcover hU hf)
        ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1) (GraphDimension.Constructions.coverPrimeGraph_codimension V W a d z) :=
  SchemeDivisor.GysinAmbient.Constructions.divisorGysinClass_ambient_Thom_of_image
    (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z (Geometric.DimensionCycles.dimensionCodimension V W + d) (GraphDimension.Constructions.parentGraph_dimension V W a Y j d)
    (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (DivisorRegularImage.Constructions.affineDivisorGraph_regularImage V W a g j hs d f z U hU) c hc
    (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph_analytic j d U hUJ)
    (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph_symm_analytic j d U hUJ) (GraphDimension.Constructions.affinePrimeGraph_codimension V W a Y j d z)
    (EtaleLocalGraph.Constructions.localGraph (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f))
    (EtaleLocalGraph.Constructions.localGraph_analytic (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f)
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates_analytic V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f))
    (EtaleLocalGraph.Constructions.localGraph_differential_injective (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f)
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates_analytic V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f))
    (NormalizationDivisor.AffineGraphClosed.Constructions.coverAffineGraph_closedEmbedding V W (Open.PrimeSupport.Constructions.ambientPrime a z) a f U hcover hU hf)
    (GraphDimension.Constructions.coverPrimeGraph_codimension V W a d z)
    (DivisorGraphImage.Constructions.affineDivisorImmersion_eq_coverGraph_image V W a g j hs d f z (Geometric.DimensionCycles.dimensionCodimension V W + d)
      (GraphDimension.Constructions.parentGraph_dimension V W a Y j d) U hU hUJ hcover)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGysin.Constructions
