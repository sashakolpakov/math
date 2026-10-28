import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.AmbientImage
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphDimension

/-! # Parent Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentCoordinates.Constructions

noncomputable section

/-! The actual parent closed-immersion Thom class becomes the polynomial normalization graph Thom class in the genuine product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions.Open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphDimension.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialNormalizationGraph.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenGraph.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.AmbientImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (a : X ⟶ AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]
  (g : X ⟶ Y) (j : Y ⟶ V.toOver) [IsOpenImmersion j.left]
  (hs : a ≫ PrincipalBoundary.Constructions.fullAmbientMap V W = g ≫ j)
  (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) (hf : Function.Surjective f)
  [IsClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f).left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d))]
  (U : Opens V.analyticSpace) (hUJ : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))

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

omit [IsAffine X.left] in
include a in
theorem parentModelDimension : Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) +
    (Geometric.DimensionCycles.dimensionCodimension V W + d) = Module.finrank ℂ (V.analyticModel × (Fin d → ℂ)) := by
  simp only [Module.finrank_prod, Module.finrank_fin_fun]
  have h := NormalizationAffine.GraphDimension.Constructions.sourceDimension_add_codimension V W a
  change Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom +
    Geometric.DimensionCycles.dimensionCodimension V W = V.complexDimension at h
  omega

theorem parentThom_productCoordinates :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ))
      (Open.AmbientImage.Constructions.imageTransportMapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f))
        (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ω) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U)
        (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ) (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (ParentGraphImage.Constructions.supportCycle V W) a U f)
        (ParentGraphImage.Constructions.parentGraph_image V W a g j hs d f U hUJ))
      (2 * (Geometric.DimensionCycles.dimensionCodimension V W + d))
      (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (Geometric.DimensionCycles.dimensionCodimension V W + d)
        (NormalizationAffine.GraphDimension.Constructions.parentGraph_dimension V W a Y j d)).regularThomClass =
      Degree.Constructions.ThomClass.complexThomClassInDegree (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (ParentGraphImage.Constructions.supportCycle V W) a U f)
        (OpenGraph.Constructions.Class.normalizationOpenGraph_analytic (ParentGraphImage.Constructions.supportCycle V W) a U (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f))
        (GraphOpenImmersion.Constructions.restrictedGraph_differential_injective (GenericFibers.Constructions.Open.openBase (ParentGraphImage.Constructions.supportCycle V W) a) (GenericFibers.Constructions.Open.openBase_analytic (ParentGraphImage.Constructions.supportCycle V W) a) U
          (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_differential_injective f hf))
        (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph_closed (ParentGraphImage.Constructions.supportCycle V W) a U f hf) (Geometric.DimensionCycles.dimensionCodimension V W + d)
        (GenericFibers.Constructions.Open.openGraph_codimension (ParentGraphImage.Constructions.supportCycle V W) a d) := by
  let Z := Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (Geometric.DimensionCycles.dimensionCodimension V W + d)
    (NormalizationAffine.GraphDimension.Constructions.parentGraph_dimension V W a Y j d)
  exact Open.AmbientImage.Constructions.ThomClass_open_ambientTransport_of_image Z.regularComplementInclusion Z.holomorphic Z.differential_injective Z.closed
    (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ)
    (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph_analytic j d U hUJ) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph_symm_analytic j d U hUJ)
    (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (ParentGraphImage.Constructions.supportCycle V W) a U f)
    (OpenGraph.Constructions.Class.normalizationOpenGraph_analytic (ParentGraphImage.Constructions.supportCycle V W) a U (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f))
    (GraphOpenImmersion.Constructions.restrictedGraph_differential_injective (GenericFibers.Constructions.Open.openBase (ParentGraphImage.Constructions.supportCycle V W) a) (GenericFibers.Constructions.Open.openBase_analytic (ParentGraphImage.Constructions.supportCycle V W) a) U
      (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_differential_injective f hf))
    (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph_closed (ParentGraphImage.Constructions.supportCycle V W) a U f hf) (Geometric.DimensionCycles.dimensionCodimension V W + d)
    Z.regularComplement_complexImmersionCodimension (GenericFibers.Constructions.Open.openGraph_codimension (ParentGraphImage.Constructions.supportCycle V W) a d)
    (parentModelDimension V W a d) (ParentGraphImage.Constructions.parentGraph_image V W a g j hs d f U hUJ)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentCoordinates.Constructions
