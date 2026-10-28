import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.DivisorGraphImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.GraphDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphClosed
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinAmbient

/-! # Divisor Gysin Thom -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.DivisorGysinThom.BundleCycles

noncomputable section

/-! The genuine affine divisor Gysin class becomes the constructed finite-support graph Thom class in polynomial product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

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
  (z : {x : X.left // Order.coheight x = 1})
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)))
  (hUJ : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

local instance finiteAffineDivisorGysinMetrizable : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteAffineDivisorGysinCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance finiteAffineDivisorGysinManifold : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

include hp hs hU in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
omit [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteDivisorPullback_mapsTo : Set.MapsTo
    (CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ))
    (Set.range (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) U
      (OpenChart.BundleCycles.finiteSupportAffineCoordinates k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) U a hcover f)))ᶜ
    (CycleClass.Thom.SchemeDivisor.Gysin.Constructions.divisorImageOpen (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d))) := by
  let Z := CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions.divisorOpenImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z (p + d)
    (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d) (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U)
    (DivisorRegularImage.BundleCycles.finiteAffineDivisorGraph_regularImage k a g j hs d f z U hU)
  intro y hy
  exact CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions.divisorOpenImmersion_mapsTo (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z (p + d)
    (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d) (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U)
    (DivisorRegularImage.BundleCycles.finiteAffineDivisorGraph_regularImage k a g j hs d f z U hU)
    (CycleClass.Thom.AmbientInverse.Constructions.ambientInverseMapsTo Z.regularComplementInclusion (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ)
      (CycleClass.Thom.ImageInvariant.Constructions.RawThom.imageMapsTo
        (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) U
          (OpenChart.BundleCycles.finiteSupportAffineCoordinates k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) U a hcover f))
        (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ ∘ Z.regularComplementInclusion)
        (DivisorGraphImage.BundleCycles.finiteAffineDivisorImmersion_eq_finiteCoverGraph_image k a g j hs d f z (p + d)
          (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d) U hU hUJ hcover) hy))

variable (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d)))
    (Set.range (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (p + d)
      (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d)).regularComplementInclusion)ᶜ) (2 * (p + d)))

variable (hc : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * (p + d)) c =
  (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (p + d)
    (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d)).regularThomClass)

omit [AlgebraicGeometry.IsNoetherian N.left] in
theorem finiteAffineDivisorGysin_eq_coverGraphThom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ))
      (finiteDivisorPullback_mapsTo k p hp a g j hs d f z U hU hUJ hcover) (2 * ((p + d) + 1))
      (CycleClass.Thom.SchemeDivisor.Gysin.Constructions.divisorGysinClass (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z (p + d)
        (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d) c hc) =
      CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree
        (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) U
          (OpenChart.BundleCycles.finiteSupportAffineCoordinates k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) U a hcover f))
        (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_analytic (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) U
          (OpenChart.BundleCycles.finiteSupportAffineCoordinates k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) U a hcover f)
          (OpenChart.BundleCycles.finiteSupportAffineCoordinates_analytic k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) U a hcover f))
        (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_differential_injective (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) U
          (OpenChart.BundleCycles.finiteSupportAffineCoordinates k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) U a hcover f)
          (OpenChart.BundleCycles.finiteSupportAffineCoordinates_analytic k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) U a hcover f))
        (FiniteSupport.AffineGraphClosed.BundleCycles.finiteSupportAffineGraph_closedEmbedding k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) a f U hcover hU hf)
        ((p + d) + 1) (GraphDimension.BundleCycles.finiteCoverPrimeGraph_codimension k p hp a d z) :=
  CycleClass.Thom.SchemeDivisor.GysinAmbient.Constructions.divisorGysinClass_ambient_Thom_of_image
    (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z (p + d) (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d)
    (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (DivisorRegularImage.BundleCycles.finiteAffineDivisorGraph_regularImage k a g j hs d f z U hU) c hc
    (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ) (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph_analytic j d U hUJ)
    (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph_symm_analytic j d U hUJ) (GraphDimension.BundleCycles.finiteAffinePrimeGraph_codimension p hp a Y j d z)
    (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) U
      (OpenChart.BundleCycles.finiteSupportAffineCoordinates k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) U a hcover f))
    (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_analytic (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) U
      (OpenChart.BundleCycles.finiteSupportAffineCoordinates k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) U a hcover f)
      (OpenChart.BundleCycles.finiteSupportAffineCoordinates_analytic k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) U a hcover f))
    (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_differential_injective (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) U
      (OpenChart.BundleCycles.finiteSupportAffineCoordinates k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) U a hcover f)
      (OpenChart.BundleCycles.finiteSupportAffineCoordinates_analytic k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) U a hcover f))
    (FiniteSupport.AffineGraphClosed.BundleCycles.finiteSupportAffineGraph_closedEmbedding k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) a f U hcover hU hf)
    (GraphDimension.BundleCycles.finiteCoverPrimeGraph_codimension k p hp a d z)
    (DivisorGraphImage.BundleCycles.finiteAffineDivisorImmersion_eq_finiteCoverGraph_image k a g j hs d f z (p + d)
      (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d) U hU hUJ hcover)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.DivisorGysinThom.BundleCycles
