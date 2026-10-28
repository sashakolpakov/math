import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.GraphProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialGraphDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport

/-! # Graph Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.GraphDimension.BundleCycles

noncomputable section

/-! Dimensions of the actual finite source, affine graph ambient, and prime image are computed from open immersion and finite support dimension formulas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialGraphDimension.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] (k : S ⟶ N) [IsFinite k.left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)

include hp in
theorem finitePrimeImage_dimension (z : {x : S.left // Order.coheight x = 1}) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S z)) N.hom + (p + 1) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom := by
  have hsrc := FiniteSupport.Cover.BundleCycles.finiteSupportSourceOver_dimension k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S z)
  have htgt := FiniteSupport.Cover.BundleCycles.finiteSupportTargetOver_dimension k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S z)
  have hc := FiniteSupport.Cover.BundleCycles.finiteSupportCover_dimensions_eq k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S z)
  have hr := CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S z))
  have hz := CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeRegularDimension_add_one S z
  have hn := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension N.hom
  omega

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (a : X ⟶ S) [IsOpenImmersion a.left]
  (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine Y.left] [IsIntegral Y.left] [Smooth Y.hom]
  (j : Y ⟶ N) [IsOpenImmersion j.left] (d : ℕ)

include hp a j in
theorem finiteAffineParentGraph_dimension : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom +
    (p + d) = Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d).hom := by
  have hs := CycleClass.Thom.PolynomialGraphDimension.Constructions.openMap_nativeDimension X a
  have ht := CycleClass.Thom.PolynomialGraphDimension.Constructions.graphTarget_ambient_dimension Y d j
  omega

include hp a j in
theorem finiteAffinePrimeGraph_codimension (z : {x : X.left // Order.coheight x = 1}) :
    CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension
      (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z)).hom) → ℂ)
      ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) = (p + d) + 1 :=
  CycleClass.Thom.PolynomialGraphDimension.Constructions.primeGraph_codimension Y d j z (p + d) (finiteAffineParentGraph_dimension p hp a Y j d)

variable [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)]

include hp in
omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteCoverPrimeGraph_codimension (z : {x : X.left // Order.coheight x = 1}) :
    CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension
      (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension
        (FiniteSupport.Cover.BundleCycles.finiteSupportSourceOver k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))).hom) → ℂ)
      ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) = (p + d) + 1 :=
  (FiniteSupport.GraphProjection.BundleCycles.finiteSupportGraph_codimension k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) (p + 1)
    (finitePrimeImage_dimension k p hp (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) d).trans (by omega)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.GraphDimension.BundleCycles
