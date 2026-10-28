import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.DivisorComplement
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentThomCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionPullback
import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo

/-! # Intersection Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.IntersectionSupport.BundleCycles

noncomputable section

/-! Every finite-support divisor graph lies in the actual parent graph intersected with the pulled-back equation support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

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

local instance finiteAffineIntersectionSupportMetrizable : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteAffineIntersectionSupportCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance finiteAffineIntersectionSupportManifold : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

abbrev finiteIntersectionCoordinateMap := CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ)

include hp hs in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [QuasiCompact a.left] in
omit [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] [IsFinite (Over.Hom.left k)] in
theorem finiteParentGraph_mapsTo : Set.MapsTo (finiteIntersectionCoordinateMap j d U hUJ)
    (Set.range (Finite.ParentGraph.BundleCycles.finiteParentGraph k a U f))ᶜ
    (Set.range (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (p + d)
      (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d)).regularComplementInclusion)ᶜ :=
  CycleClass.Thom.Open.AmbientImage.Constructions.imageTransportMapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f))
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ω) (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U)
    (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ) (Finite.ParentGraph.BundleCycles.finiteParentGraph k a U f)
    (Finite.ParentGraph.BundleCycles.finiteParentGraph_image k a g j hs d f U hUJ)

variable {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d))
  (R : X.left.Opens) (z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R)
  (hR : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ⁻¹' (Set.range v)ᶜ ⊆
    (CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X R : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
include hp hs hR hU in
omit [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteIntersectionDivisor_mapsTo : Set.MapsTo (𝟙 (TopCat.of (U × (Fin d → ℂ))))
    (Set.range (Finite.ParentGraph.BundleCycles.finiteParentGraph k a U f) ∩
      Set.range (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (finiteIntersectionCoordinateMap j d U hUJ) v))ᶜ
    (Set.range (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))
      (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))) U
      (OpenChart.BundleCycles.finiteSupportAffineCoordinates k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U a hcover f)))ᶜ := by
  intro y hy
  apply (Set.ext_iff.mp (DivisorComplement.BundleCycles.finiteAffineDivisorGraph_complement k p hp a g j hs d f ⟨z.val, z.property.1⟩ U hU hUJ hcover) y).mp
  exact CycleClass.Thom.SchemeDivisor.IntersectionPullback.Constructions.pullbackDivisor_mapsTo (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (p + d)
    (GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d) v
    (Finite.ParentGraph.BundleCycles.finiteParentGraph k a U f) (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (finiteIntersectionCoordinateMap j d U hUJ) v)
    (finiteIntersectionCoordinateMap j d U hUJ) (finiteParentGraph_mapsTo k p hp a g j hs d f U hUJ)
    (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (finiteIntersectionCoordinateMap j d U hUJ) v) R z hR hy

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.IntersectionSupport.BundleCycles
