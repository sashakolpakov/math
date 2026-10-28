import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.IntersectionSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.AffineDivisorGysinProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.GraphBaseRange
import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.BothSupportEnlargement

/-! # Divisor Common Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.DivisorCommonProjection.BundleCycles

noncomputable section

/-! Each actual divisor graph projects into the common intersection support with its true residue degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Projection.BothSupportEnlargement.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

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

local instance finiteAffineDivisorCommonProjectionMetrizable : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteAffineDivisorCommonProjectionCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance finiteAffineDivisorCommonProjectionManifold : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

variable {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d))
  (R : X.left.Opens) (z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R)
  (hR : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ⁻¹' (Set.range v)ᶜ ⊆
    (CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X R : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))

include hp hs hR hU in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
omit [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteDivisorGraph_le_intersection :
    Set.range (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))
      (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))) U
      (OpenChart.BundleCycles.finiteSupportAffineCoordinates k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U a hcover f)) ⊆
    Set.range (Finite.ParentGraph.BundleCycles.finiteParentGraph k a U f) ∩
      Set.range (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ) v) := by
  intro y hy
  by_contra hn
  exact IntersectionSupport.BundleCycles.finiteIntersectionDivisor_mapsTo k p hp a g j hs d f U hUJ hcover v R z hR hU hn hy

variable (T : Set U) (K : Set (Fin d → ℂ)) (hK : IsCompact K)
  (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U →
    CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K)
  (hT : Set.range (Finite.ParentGraph.BundleCycles.finiteParentGraph k a U f) ∩
    Set.range (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ) v) ⊆ T ×ˢ K)

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
include hp hs hR hT hcover in
theorem finiteDivisorImage_le_commonSupport :
    Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))) U
      (hU.trans (FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen_target_regular k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))))) ⊆ T :=
  FiniteSupport.GraphBaseRange.BundleCycles.finiteSupportImage_le_of_graph_bound k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U hU
    (OpenChart.BundleCycles.finiteSupportAffineCoordinates k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U a hcover f) T K
    ((finiteDivisorGraph_le_intersection k p hp a g j hs d f U hUJ hcover v R z hR hU).trans hT)

include hb in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem finiteDivisorGraphThom_project_commonSupport :
    CycleClass.Thom.Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) T K hK
      (Set.range (Finite.ParentGraph.BundleCycles.finiteParentGraph k a U f) ∩
        Set.range (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ) v)) hT
      (2 * (p + 1)) (2 * ((p + d) + 1)) (by omega)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (U × (Fin d → ℂ))))
        (IntersectionSupport.BundleCycles.finiteIntersectionDivisor_mapsTo k p hp a g j hs d f U hUJ hcover v R z hR hU)
        (2 * ((p + d) + 1))
        (Finite.AffineDivisorGysinProjection.BundleCycles.finiteDivisorGraphThomClass k p hp a d f hf ⟨z.val, z.property.1⟩ U hU hcover)) =
    (k.left.residueDegree (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ) •
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
        (A := Tᶜ)
        (B := (Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))) U
          (hU.trans (FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen_target_regular k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))))))ᶜ)
        (fun _ hx hy => hx (finiteDivisorImage_le_commonSupport k p hp a g j hs d f U hUJ hcover v R z hR hU T K hT hy))
        (2 * (p + 1))
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
          (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_mapsTo N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))) U
            (hU.trans (FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen_target_regular k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))))
          (2 * (p + 1))
          (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))) (p + 1) (GraphDimension.BundleCycles.finitePrimeImage_dimension k p hp (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))) := by
  have h := CycleClass.Thom.Projection.BothSupportEnlargement.Constructions.projectAt_support_enlargement d (TopCat.of U)
    (Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))) U
      (hU.trans (FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen_target_regular k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))))) T
    (finiteDivisorImage_le_commonSupport k p hp a g j hs d f U hUJ hcover v R z hR hU T K hT) K hK
    (Set.range (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))
      (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))) U
      (OpenChart.BundleCycles.finiteSupportAffineCoordinates k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U a hcover f)))
    (Set.range (Finite.ParentGraph.BundleCycles.finiteParentGraph k a U f) ∩
      Set.range (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ) v))
    (FiniteSupport.AffineGraphClass.BundleCycles.finiteSupportAffineGraph_bound k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U hU a hcover f K hb) hT
    (finiteDivisorGraph_le_intersection k p hp a g j hs d f U hUJ hcover v R z hR hU)
    (2 * (p + 1)) (2 * ((p + d) + 1)) (by omega)
    (Finite.AffineDivisorGysinProjection.BundleCycles.finiteDivisorGraphThomClass k p hp a d f hf ⟨z.val, z.property.1⟩ U hU hcover)
  refine h.trans ?_
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U)) _ _
    (Finite.AffineDivisorGysinProjection.BundleCycles.finiteAffineDivisorProjection k p a d f ⟨z.val, z.property.1⟩ U hU hcover K hK hb
      (Finite.AffineDivisorGysinProjection.BundleCycles.finiteDivisorGraphThomClass k p hp a d f hf ⟨z.val, z.property.1⟩ U hU hcover)) = _
  rw [Finite.AffineDivisorGysinProjection.BundleCycles.finiteDivisorGraphThom_project_imageCycleClass k p hp a d f hf ⟨z.val, z.property.1⟩ U hU hcover K hK hb, map_smul]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.DivisorCommonProjection.BundleCycles
