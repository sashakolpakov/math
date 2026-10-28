import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentGraph
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.DivisorGysinThom
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.AmbientImage

/-! # Parent Thom Coordinates -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentThomCoordinates.BundleCycles

noncomputable section

/-! The actual parent closed-immersion Thom class is the polynomial parent graph Thom class in product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.AmbientImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions

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

local instance finiteParentThomMetrizable : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteParentThomCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance finiteParentThomManifold : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

def finiteParentGraphThomClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U × (Fin d → ℂ)))
      (Set.range (ParentGraph.BundleCycles.finiteParentGraph k a U f))ᶜ (2 * (p + d)) :=
  CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree (ParentGraph.BundleCycles.finiteParentGraph k a U f) (ParentGraph.BundleCycles.finiteParentGraph_analytic k a U f)
    (ParentGraph.BundleCycles.finiteParentGraph_differential_injective k a U f hf) (ParentGraph.BundleCycles.finiteParentGraph_closed k a U f hf)
    (p + d) (ParentGraph.BundleCycles.finiteParentGraph_codimension a (d := d) p hp)

omit [AlgebraicGeometry.IsNoetherian N.left] [IsFinite (Over.Hom.left k)] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [QuasiCompact (Over.Hom.left a)] in
theorem finiteParentThom_productCoordinates :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ))
      (CycleClass.Thom.Open.AmbientImage.Constructions.imageTransportMapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f))
        (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ω) (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U)
        (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ) (ParentGraph.BundleCycles.finiteParentGraph k a U f)
        (ParentGraph.BundleCycles.finiteParentGraph_image k a g j hs d f U hUJ))
      (2 * (p + d))
      (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (p + d)
        (FiniteAffine.GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d)).regularThomClass =
      finiteParentGraphThomClass k p hp a d f hf U := by
  let Z := CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) (p + d)
    (FiniteAffine.GraphDimension.BundleCycles.finiteAffineParentGraph_dimension p hp a Y j d)
  exact CycleClass.Thom.Open.AmbientImage.Constructions.ThomClass_open_ambientTransport_of_image Z.regularComplementInclusion Z.holomorphic Z.differential_injective Z.closed
    (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ)
    (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph_analytic j d U hUJ) (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph_symm_analytic j d U hUJ)
    (ParentGraph.BundleCycles.finiteParentGraph k a U f) (ParentGraph.BundleCycles.finiteParentGraph_analytic k a U f)
    (ParentGraph.BundleCycles.finiteParentGraph_differential_injective k a U f hf) (ParentGraph.BundleCycles.finiteParentGraph_closed k a U f hf) (p + d)
    Z.regularComplement_complexImmersionCodimension (ParentGraph.BundleCycles.finiteParentGraph_codimension a (d := d) p hp)
    (ParentGraph.BundleCycles.finiteParentGraph_modelDimension a (d := d) p hp) (ParentGraph.BundleCycles.finiteParentGraph_image k a g j hs d f U hUJ)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentThomCoordinates.BundleCycles
