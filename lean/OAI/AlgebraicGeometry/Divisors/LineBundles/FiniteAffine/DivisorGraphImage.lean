import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.DivisorRegularImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.PrimeGraphRange
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage

/-! # Divisor Graph Image -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.DivisorGraphImage.BundleCycles

noncomputable section

/-! The actual divisor Gysin immersion has exactly the constructed finite-support cover graph as its image in product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeRegularRange.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] (k : S ⟶ N) [IsFinite k.left]

open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (a : X ⟶ S) [IsOpenImmersion a.left] [QuasiCompact a.left]
  (g : X ⟶ Y) (j : Y ⟶ N) [IsOpenImmersion j.left]
  (hs : a ≫ k = g ≫ j)
  (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  [IsClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f).left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d))]
  (z : {x : X.left // Order.coheight x = 1}) (q : ℕ)
  (hq : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + q =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d).hom)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)))
  (hUJ : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

theorem finiteAffineDivisorImmersion_eq_finiteCoverGraph_image :
    Set.range (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ ∘
      (CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions.divisorOpenImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z q hq (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U)
        (DivisorRegularImage.BundleCycles.finiteAffineDivisorGraph_regularImage k a g j hs d f z U hU)).regularComplementInclusion) =
      Set.range (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) U
        (OpenChart.BundleCycles.finiteSupportAffineCoordinates k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) U a hcover f)) :=
  (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.divisorOpenImmersion_fullGraphImage j d g f z q hq U hUJ
    (DivisorRegularImage.BundleCycles.finiteAffineDivisorGraph_regularImage k a g j hs d f z U hU)).trans
      ((PrimeGraphRange.BundleCycles.finiteAffinePrimeGraphImage_eq_fullSupportGraph k a g j hs z f U).symm.trans
        (FiniteSupport.AffineGraphRange.BundleCycles.finiteSupportAffineGraph_range k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) a f U hcover hU).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.DivisorGraphImage.BundleCycles
