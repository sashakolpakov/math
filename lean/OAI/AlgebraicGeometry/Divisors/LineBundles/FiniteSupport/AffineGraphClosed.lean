import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphRange
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphEmbedding

/-! # Affine Graph Closed -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphClosed.BundleCycles

noncomputable section

/-! The constructed graph is closed because it is exactly the full closed support graph in the affine source. -/

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

omit [IsOpenImmersion a.left] [IsIntegral X.left] [Smooth X.hom] in
omit [AlgebraicGeometry.IsIntegral S.left] [Smooth S.hom] in
theorem finiteSupportAffineSupportSet_closed : IsClosed (AffineGraphRange.BundleCycles.finiteSupportAffineSupportSet Z a) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient S Z)).isClosed_range.preimage
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map a)

variable [IsAffine X.left] {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  [T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]

omit [IsOpenImmersion a.left] [IsIntegral X.left] [Smooth X.hom] in
omit [AlgebraicGeometry.IsIntegral S.left] [Smooth S.hom] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [IsFinite (Over.Hom.left g)] in
theorem finiteSupportAffineFullGraph_closedEmbedding (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding (AffineGraphRange.BundleCycles.finiteSupportAffineFullGraph g a f) :=
  CycleClass.Thom.Closed.GraphEmbedding.Constructions.graph_closedEmbedding (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a)
    ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map g).comp (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map a))
    (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_closedEmbedding f hf)

variable (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))

omit [IsOpenImmersion a.left] [IsIntegral X.left] [Smooth X.hom] in
omit [AlgebraicGeometry.IsIntegral S.left] [Smooth S.hom] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [IsFinite (Over.Hom.left g)] in
theorem finiteSupportAffineGraphImage_closed (hf : Function.Surjective f) :
    IsClosed (AffineGraphRange.BundleCycles.finiteSupportAffineGraphImage g Z a f U) :=
  ((finiteSupportAffineFullGraph_closedEmbedding g a f hf).isClosedMap _ (finiteSupportAffineSupportSet_closed Z a)).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem finiteSupportAffineGraph_closedEmbedding
    (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))
    (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆ Cover.BundleCycles.finiteSupportRetainedOpen g Z) (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (Cover.BundleCycles.finiteSupportCoverMap g Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap g Z) U
      (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates g Z U a hcover f)) := by
  refine ⟨AffineGraphEmbedding.BundleCycles.finiteSupportAffineGraph_isEmbedding g Z a U hcover f hf, ?_⟩
  rw [AffineGraphRange.BundleCycles.finiteSupportAffineGraph_range g Z a f U hcover hU]
  exact finiteSupportAffineGraphImage_closed g Z a f U hf

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphClosed.BundleCycles
