import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.OpenChart

/-! # Affine Graph Embedding -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphEmbedding.BundleCycles

noncomputable section

/-! Polynomial coordinates of the genuine affine source embed the lifted support cover and its local graph. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.GraphEmbedding.Constructions

variable {S Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (g : S ⟶ Y) [IsFinite g.left]
  (Z : IrreducibleCloseds S.left)
  {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (a : X ⟶ S) [IsOpenImmersion a.left]

variable (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

theorem finiteSupportAffineLift_isEmbedding : Topology.IsEmbedding (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineLift g Z U a hcover) := by
  apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion a).isEmbedding.of_comp_iff.mp
  have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a ∘ FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineLift g Z U a hcover =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportSourceAmbientMap g Z) ∘
        (Subtype.val : FiniteAffine.OpenChart.BundleCycles.finiteSupportLocalSource g Z U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Cover.BundleCycles.finiteSupportSourceOver g Z)) := by
    funext x
    exact FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineLift_commutes g Z U a hcover x
  rw [he]
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (Cover.BundleCycles.finiteSupportSourceAmbientMap g Z)).comp .subtypeVal

variable [IsAffine X.left] {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

theorem finiteSupportAffineCoordinates_isEmbedding (hf : Function.Surjective f) :
    Topology.IsEmbedding (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates g Z U a hcover f) :=
  (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_closedEmbedding f hf).isEmbedding.comp (finiteSupportAffineLift_isEmbedding g Z a U hcover)

local instance (priority := low) finiteSupportAffineGraphEmbeddingCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)

theorem finiteSupportAffineGraph_isEmbedding (hf : Function.Surjective f) :
    Topology.IsEmbedding (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (Cover.BundleCycles.finiteSupportCoverMap g Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap g Z) U
      (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates g Z U a hcover f)) :=
  Topology.IsEmbedding.of_comp
    (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph_analytic (Cover.BundleCycles.finiteSupportCoverMap g Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap g Z) U
      (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates g Z U a hcover f) (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates_analytic g Z U a hcover f)).continuous
    (continuous_snd : Continuous (Prod.snd : U × (Fin d → ℂ) → (Fin d → ℂ)))
    (finiteSupportAffineCoordinates_isEmbedding g Z a U hcover f hf)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphEmbedding.BundleCycles
