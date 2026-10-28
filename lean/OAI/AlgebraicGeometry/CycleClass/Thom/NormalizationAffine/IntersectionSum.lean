import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphClasses

/-! # Intersection Sum -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionSum.Constructions

noncomputable section

/-! The actual polynomial normalization parent Thom class intersected with an equation is the sum of the constructed divisor graph Thom classes, with literal scheme orders and common support. -/

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

include hr her in
theorem imageIntersectionCup_eq_order_coverGraphThom_sum :
    ImageIntersectionCup.Constructions.imageIntersectionCup (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f)
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v)
      (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph_closed (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f hf).isClosed_range.isOpen_compl
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v hv) (Geometric.DimensionCycles.dimensionCodimension V W + d) 1
      (GraphClasses.Constructions.parentGraphThomClass V W a d f hf U)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (IntersectionSupport.Constructions.coordinateMap V j d U hUJ)
        (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v) 2
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) e he 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1))) =
    ∑ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain, (X.left.ord r z.val : ℚ) •
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (U × (Fin d → ℂ))))
        (IntersectionSupport.Constructions.intersectionDivisor_mapsTo V W a g j hs d f U hUJ hcover v D.domain z hD (hU z))
        (2 * ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1))
        (GraphClasses.Constructions.divisorGraphThomClass V W a d f hf ⟨z.val, z.property.1⟩ U (hU z) hcover) := by
  classical
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d)))
      (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (Geometric.DimensionCycles.dimensionCodimension V W + d)
        (GraphDimension.Constructions.parentGraph_dimension V W a Y j d)).regularComplementInclusion)ᶜ)
    (2 * (Geometric.DimensionCycles.dimensionCodimension V W + d))
    (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (Geometric.DimensionCycles.dimensionCodimension V W + d)
      (GraphDimension.Constructions.parentGraph_dimension V W a Y j d)).regularThomClass
  have h := SchemeDivisor.IntersectionPullback.Constructions.imageIntersectionCup_pullback_eq_order_globalGysin_sum (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f)
    (Geometric.DimensionCycles.dimensionCodimension V W + d) (GraphDimension.Constructions.parentGraph_dimension V W a Y j d) v
    (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f)
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v) (IntersectionSupport.Constructions.coordinateMap V j d U hUJ)
    (IntersectionSupport.Constructions.parentGraph_mapsTo V W a g j hs d f U hUJ) (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v)
    c hc hv (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph_closed (Normalization.ParentGraphImage.Constructions.supportCycle V W) a U f hf).isClosed_range.isOpen_compl
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v hv) D hr hD e he her
  have hparent := Normalization.ParentCoordinates.Constructions.parentThom_productCoordinates V W a g j hs d f hf U hUJ
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (IntersectionSupport.Constructions.coordinateMap V j d U hUJ)
    (IntersectionSupport.Constructions.parentGraph_mapsTo V W a g j hs d f U hUJ) (2 * (Geometric.DimensionCycles.dimensionCodimension V W + d))
    (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (Geometric.DimensionCycles.dimensionCodimension V W + d)
      (GraphDimension.Constructions.parentGraph_dimension V W a Y j d)).regularThomClass = GraphClasses.Constructions.parentGraphThomClass V W a d f hf U at hparent
  rw [hparent] at h
  refine h.trans (Finset.sum_congr rfl ?_)
  intro z _
  apply congrArg (fun b => (X.left.ord r z.val : ℚ) • b)
  have ht := DivisorGysin.Constructions.affineDivisorGysin_eq_coverGraphThom V W a g j hs d f hf ⟨z.val, z.property.1⟩
    U (hU z) hUJ hcover c hc
  have hm := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (U × (Fin d → ℂ))))
      (IntersectionSupport.Constructions.coordinateMap V j d U hUJ)
      (IntersectionSupport.Constructions.intersectionDivisor_mapsTo V W a g j hs d f U hUJ hcover v D.domain z hD (hU z))
      (DivisorGysin.Constructions.divisorPullback_mapsTo V W a g j hs d f ⟨z.val, z.property.1⟩ U (hU z) hUJ hcover)
      (2 * ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1)))
    (SchemeDivisor.Gysin.Constructions.divisorGysinClass (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ⟨z.val, z.property.1⟩ (Geometric.DimensionCycles.dimensionCodimension V W + d)
      (GraphDimension.Constructions.parentGraph_dimension V W a Y j d) c hc)
  exact hm.symm.trans (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of (U × (Fin d → ℂ))))
    (IntersectionSupport.Constructions.intersectionDivisor_mapsTo V W a g j hs d f U hUJ hcover v D.domain z hD (hU z))
    (2 * ((Geometric.DimensionCycles.dimensionCodimension V W + d) + 1))) ht)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionSum.Constructions
