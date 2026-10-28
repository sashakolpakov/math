import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionSum
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorCommonProjection

/-! # Intersection Projection Sum -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionProjectionSum.Constructions

noncomputable section

/-! The actual normalization graph equation intersection projects to the sum of the original ambient image-cycle classes, with literal source orders times actual residue degrees, in a common supported group. -/

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
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGysin.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction

variable {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d)) (hv : IsOpen (Set.range v)ᶜ)
  {r : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left r) (hr : r ≠ 0)
  (hD : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ⁻¹' (Set.range v)ᶜ ⊆
    (Scheme.SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
  (hU : ∀ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain,
    (U : Set V.analyticSpace) ⊆ NormalizationDivisor.GraphOpen.Constructions.goodAmbient V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))
  (e : TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d)) ⟶ PrincipalBoundary.Constructions.normalComplexLine)
  (he : Set.MapsTo e (Set.range v)ᶜ PrincipalBoundary.Constructions.puncturedComplexLine)
  (her : ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ⁻¹' (Set.range v)ᶜ,
    e (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) x.val) 0 = Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X D.domain
      (D.unit : Γ(X.left, D.domain)) ⟨x.val, hD x.property⟩)

local instance : Fintype (Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain) := Fintype.ofFinite _

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionSum.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorCommonProjection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Image.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions

variable (S : Set U) (K : Set (Fin d → ℂ)) (hK : IsCompact K)
  (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U →
    Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K)
  (hT : Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f) ∩
    Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v) ⊆ S ×ˢ K)

include hr her hb in
theorem graphIntersection_project_order_imageCycle_sum :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) S K hK
      (Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f) ∩
        Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v)) hT
      (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1)) (2 * ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1)) (by omega)
      (ImageIntersectionCup.Constructions.imageIntersectionCup (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f)
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v)
      (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph_closed (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f hf).isClosed_range.isOpen_compl
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v hv) (Geometric.DimensionCycles.dimensionCodimension V W + d) 1
      (GraphClasses.Constructions.parentGraphThomClass V W a d f hf U)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (IntersectionSupport.Constructions.coordinateMap V j d U hUJ)
        (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v) 2
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) e he 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)))) =
    ∑ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain, (X.left.ord r z.val : ℚ) •
      (((Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ) •
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
        (A := Sᶜ)
        (B := (Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
          ((hU z).trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))))ᶜ)
        (fun _ hx hy => hx (DivisorCommonProjection.Constructions.divisorImage_le_commonSupport V W a g j hs d f U hUJ hcover v D.domain z hD (hU z) S K hT hy))
        (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1))
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
          (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_mapsTo (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
            ((hU z).trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))))
          (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1))
          (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)).rationalSupportedCycleClass)) := by
  classical
  have h := congrArg
    (Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) S K hK
      (Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f) ∩
        Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v)) hT
      (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1)) (2 * ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1)) (by omega))
    (IntersectionSum.Constructions.imageIntersectionCup_eq_order_coverGraphThom_sum V W a g j hs d f hf U hUJ hcover v hv D hr hD hU e he her)
  simp only [map_sum, map_smul] at h
  refine h.trans (Finset.sum_congr rfl ?_)
  intro z _
  exact congrArg (fun b => (X.left.ord r z.val : ℚ) • b)
    (DivisorCommonProjection.Constructions.divisorGraphThom_project_commonSupport V W a g j hs d f hf U hUJ hcover v D.domain z hD (hU z) S K hK hb hT)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionProjectionSum.Constructions
