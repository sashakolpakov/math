import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphClosed
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.LocalGraphProjection

/-! # Affine Graph Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphClass.BundleCycles

noncomputable section

/-! An actual polynomial affine chart supplies all graph hypotheses. Supported projection has exactly the finite map's residue degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

variable {S Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] (g : S ⟶ Y) [IsFinite g.left]
  (Z : IrreducibleCloseds S.left) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆ Cover.BundleCycles.finiteSupportRetainedOpen g Z)
  {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  (a : X ⟶ S) [IsOpenImmersion a.left]
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))
  {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

local instance finiteSupportAffineGraphClassMetrizable : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteSupportAffineGraphClassCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance finiteSupportAffineGraphClassManifold : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

theorem finiteSupportAffineGraph_bound (K : Set (Fin d → ℂ))
    (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U →
      CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K) :
    Set.range (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (Cover.BundleCycles.finiteSupportCoverMap g Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap g Z) U
      (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates g Z U a hcover f)) ⊆
      Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport g Z) U
        (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular g Z))) ×ˢ K := by
  rintro _ ⟨x, rfl⟩
  refine ⟨?_, FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates_bound g Z U a hcover f K hb x⟩
  rw [← GraphProjection.BundleCycles.finiteSupportTargetAmbientMap_regular_range g Z U hU]
  exact ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportCoverMap g Z) x.val, rfl⟩

variable (p : ℕ)
  (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport g Z) Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
  (hf : Function.Surjective f)

theorem finiteSupportAffineGraph_project_cycleClass
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U →
      CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K) :
    CycleClass.Thom.Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) (Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport g Z) U
      (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular g Z)))) K hK
      (Set.range (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (Cover.BundleCycles.finiteSupportCoverMap g Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap g Z) U (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates g Z U a hcover f))) (finiteSupportAffineGraph_bound g Z U hU a hcover f K hb)
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (Cover.BundleCycles.finiteSupportCoverMap g Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap g Z) U (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates g Z U a hcover f))
        (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_analytic (Cover.BundleCycles.finiteSupportCoverMap g Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap g Z) U (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates g Z U a hcover f) (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates_analytic g Z U a hcover f))
        (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_differential_injective (Cover.BundleCycles.finiteSupportCoverMap g Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap g Z) U (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates g Z U a hcover f) (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates_analytic g Z U a hcover f))
        (AffineGraphClosed.BundleCycles.finiteSupportAffineGraph_closedEmbedding g Z a f U hcover hU hf) (p + d) (GraphProjection.BundleCycles.finiteSupportGraph_codimension g Z p hp d)) =
    (g.left.residueDegree (irreducibleSetEquivPoints Z) : ℚ) •
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
        (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_mapsTo Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport g Z) U
          (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular g Z))) (2 * p)
        (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport g Z) p hp) :=
  LocalGraphProjection.BundleCycles.finiteSupportLocalGraph_project_cycleClass g Z U hU p hp
    (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates g Z U a hcover f)
    (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates_analytic g Z U a hcover f)
    (AffineGraphClosed.BundleCycles.finiteSupportAffineGraph_closedEmbedding g Z a f U hcover hU hf)
    K hK (finiteSupportAffineGraph_bound g Z U hU a hcover f K hb)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphClass.BundleCycles
