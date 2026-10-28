import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGysin
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentCoordinates

/-! # Graph Classes -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphClasses.Constructions

noncomputable section

/-! Short names for the already constructed actual parent and divisor graph Thom classes. -/

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

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialNormalizationGraph.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenGraph.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions.Open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

def parentGraphThomClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U × (Fin d → ℂ)))
    (Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f))ᶜ (2 * (Geometric.DimensionCycles.dimensionCodimension V W + d)) :=
  Degree.Constructions.ThomClass.complexThomClassInDegree (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f)
    (Normalization.OpenGraph.Constructions.Class.normalizationOpenGraph_analytic (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f))
    (GraphOpenImmersion.Constructions.restrictedGraph_differential_injective (Normalization.GenericFibers.Constructions.Open.openBase (Normalization.ParentGraphImage.Constructions.supportCycle V W) a) (Normalization.GenericFibers.Constructions.Open.openBase_analytic (Normalization.ParentGraphImage.Constructions.supportCycle V W) a) U
      (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_differential_injective f hf))
    (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph_closed (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f hf) (Geometric.DimensionCycles.dimensionCodimension V W + d)
    (Normalization.GenericFibers.Constructions.Open.openGraph_codimension (Normalization.ParentGraphImage.Constructions.supportCycle V W) a d)

def divisorGraphThomClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U × (Fin d → ℂ)))
    (Set.range (EtaleLocalGraph.Constructions.localGraph (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
      (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f)))ᶜ (2 * ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1)) :=
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
    ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1) (GraphDimension.Constructions.coverPrimeGraph_codimension V W a d z)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphClasses.Constructions
