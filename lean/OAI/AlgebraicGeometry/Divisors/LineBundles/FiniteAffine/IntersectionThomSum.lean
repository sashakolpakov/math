import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.IntersectionSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.AffineDivisorGysinProjection

/-! # Intersection Thom Sum -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.IntersectionThomSum.BundleCycles

noncomputable section

/-! The actual parent graph equation intersection is the sum of its genuine divisor graph Thom classes, with literal source orders and common support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.AmbientImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionPullback.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinAmbient.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport OAI.AlgebraicGeometry.CycleClass.Thom.AmbientInverse.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] [AlgebraicGeometry.IsNoetherian N.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] (k : S ⟶ N) [IsFinite k.left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (a : X ⟶ S) [IsOpenImmersion a.left] [QuasiCompact a.left]
  (g : X ⟶ Y) (j : Y ⟶ N) [IsOpenImmersion j.left]
  (hs : a ≫ k = g ≫ j)
  (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) (hf : Function.Surjective f)
  [IsClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f).left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d))]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hUJ : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

local instance finiteAffineIntersectionThomSumMetrizable : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteAffineIntersectionThomSumCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance finiteAffineIntersectionThomSumManifold : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

variable {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d)) (hv : IsOpen (Set.range v)ᶜ)
  {r : X.left.functionField} (D : CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left r) (hr : r ≠ 0)
  (hD : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ⁻¹' (Set.range v)ᶜ ⊆
    (CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
  (hU : ∀ z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain,
    (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))
  (e : TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d)) ⟶ CycleClass.Thom.PrincipalBoundary.Constructions.normalComplexLine)
  (he : Set.MapsTo e (Set.range v)ᶜ CycleClass.Thom.PrincipalBoundary.Constructions.puncturedComplexLine)
  (her : ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ⁻¹' (Set.range v)ᶜ,
    e (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) x.val) 0 = CycleClass.Thom.Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X D.domain
      (D.unit : Γ(X.left, D.domain)) ⟨x.val, hD x.property⟩)

local instance finiteAffineIntersectionThomSumFintype : Fintype (CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain) := Fintype.ofFinite _

include hr her in
omit [AlgebraicGeometry.IsNoetherian N.left] in
theorem finiteImageIntersectionCup_eq_order_coverGraphThom_sum :
    CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup (Finite.ParentGraph.BundleCycles.finiteParentGraph k a U f)
      (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ) v)
      (Finite.ParentGraph.BundleCycles.finiteParentGraph_closed k a U f hf).isClosed_range.isOpen_compl
      (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ) v hv) (p + d) 1
      (Finite.ParentThomCoordinates.BundleCycles.finiteParentGraphThomClass k p hp a d f hf U)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ)
        (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ) v) 2
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) e he 2 (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1))) =
    ∑ z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain, (X.left.ord r z.val : ℚ) •
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (U × (Fin d → ℂ))))
        (IntersectionSupport.BundleCycles.finiteIntersectionDivisor_mapsTo k p hp a g j hs d f U hUJ hcover v D.domain z hD (hU z))
        (2 * ((p + d) + 1))
        (Finite.AffineDivisorGysinProjection.BundleCycles.finiteDivisorGraphThomClass k p hp a d f hf ⟨z.val, z.property.1⟩ U (hU z) hcover) := by
  classical
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d)))
      (Set.range (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (p + d)
        (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d)).regularComplementInclusion)ᶜ)
    (2 * (p + d))
    (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (p + d)
      (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d)).regularThomClass
  have h := CycleClass.Thom.SchemeDivisor.IntersectionPullback.Constructions.imageIntersectionCup_pullback_eq_order_globalGysin_sum (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f)
    (p + d) (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d) v
    (Finite.ParentGraph.BundleCycles.finiteParentGraph k a U f)
    (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ) v) (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ)
    (IntersectionSupport.BundleCycles.finiteParentGraph_mapsTo k p hp a g j hs d f U hUJ) (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ) v)
    c hc hv (Finite.ParentGraph.BundleCycles.finiteParentGraph_closed k a U f hf).isClosed_range.isOpen_compl
    (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ) v hv) D hr hD e he her
  have hparent := Finite.ParentThomCoordinates.BundleCycles.finiteParentThom_productCoordinates k p hp a g j hs d f hf U hUJ
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ)
    (IntersectionSupport.BundleCycles.finiteParentGraph_mapsTo k p hp a g j hs d f U hUJ) (2 * (p + d))
    (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (p + d)
      (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d)).regularThomClass = Finite.ParentThomCoordinates.BundleCycles.finiteParentGraphThomClass k p hp a d f hf U at hparent
  rw [hparent] at h
  refine h.trans (Finset.sum_congr rfl ?_)
  intro z _
  apply congrArg (fun b => (X.left.ord r z.val : ℚ) • b)
  have ht := DivisorGysinThom.BundleCycles.finiteAffineDivisorGysin_eq_coverGraphThom k p hp a g j hs d f hf ⟨z.val, z.property.1⟩
    U (hU z) hUJ hcover c hc
  have hm := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (U × (Fin d → ℂ))))
      (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ)
      (IntersectionSupport.BundleCycles.finiteIntersectionDivisor_mapsTo k p hp a g j hs d f U hUJ hcover v D.domain z hD (hU z))
      (DivisorGysinThom.BundleCycles.finiteDivisorPullback_mapsTo k p hp a g j hs d f ⟨z.val, z.property.1⟩ U (hU z) hUJ hcover)
      (2 * ((p + d) + 1)))
    (CycleClass.Thom.SchemeDivisor.Gysin.Constructions.divisorGysinClass (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ⟨z.val, z.property.1⟩ (p + d)
      (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d) c hc)
  exact hm.symm.trans (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of (U × (Fin d → ℂ))))
    (IntersectionSupport.BundleCycles.finiteIntersectionDivisor_mapsTo k p hp a g j hs d f U hUJ hcover v D.domain z hD (hU z))
    (2 * ((p + d) + 1))) ht)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.IntersectionThomSum.BundleCycles
