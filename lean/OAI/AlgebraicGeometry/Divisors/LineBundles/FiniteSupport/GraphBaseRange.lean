import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphClass
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.IntrinsicFiniteSurjective

/-! # Graph Base Range -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.GraphBaseRange.BundleCycles

noncomputable section

/-! The first-coordinate image of the actual finite support graph is the full image support over the retained open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.IntrinsicFiniteSurjective.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] [AlgebraicGeometry.IsNoetherian N.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] (k : S ⟶ N) [IsFinite k.left]
  (Z : IrreducibleCloseds S.left) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Cover.BundleCycles.finiteSupportRetainedOpen k Z)

variable {d : ℕ} (e : FiniteAffine.OpenChart.BundleCycles.finiteSupportLocalSource k Z U → Fin d → ℂ)

omit [AlgebraicGeometry.IsIntegral S.left] [Smooth S.hom] in
theorem finiteSupportLocalGraph_firstRange :
    Set.range (Prod.fst ∘ CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (Cover.BundleCycles.finiteSupportCoverMap k Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap k Z) U e) =
      Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k Z) U (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular k Z))) := by
  rw [← GraphProjection.BundleCycles.finiteSupportTargetAmbientMap_regular_range k Z U hU]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportCoverMap k Z) x.val, rfl⟩
  · rintro ⟨t, ht⟩
    obtain ⟨x, hx⟩ := CycleClass.Thom.Integral.IntrinsicFiniteSurjective.Constructions.Intrinsic.nativeMap_surjective (Cover.BundleCycles.finiteSupportCoverMap k Z) (Cover.BundleCycles.finiteSupportCoverMap_genericPoint k Z) t
    have hxy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportTargetAmbientMap k Z)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportCoverMap k Z) x) = y.val := (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportTargetAmbientMap k Z)) hx).trans ht
    have hxU : CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase (Cover.BundleCycles.finiteSupportCoverMap k Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap k Z) x ∈ U := by
      change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportTargetAmbientMap k Z)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Cover.BundleCycles.finiteSupportCoverMap k Z) x) ∈ U
      rw [hxy]
      exact y.property
    exact ⟨⟨x, hxU⟩, Subtype.ext hxy⟩

omit [AlgebraicGeometry.IsIntegral S.left] [Smooth S.hom] in
theorem finiteSupportImage_le_of_graph_bound (S : Set U) (K : Set (Fin d → ℂ))
    (hb : Set.range (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (Cover.BundleCycles.finiteSupportCoverMap k Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap k Z) U e) ⊆ S ×ˢ K) :
    Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k Z) U (hU.trans (Cover.BundleCycles.finiteSupportRetainedOpen_target_regular k Z))) ⊆ S := by
  rw [← finiteSupportLocalGraph_firstRange k Z U hU e]
  rintro _ ⟨x, rfl⟩
  exact (hb ⟨x, rfl⟩).1

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.GraphBaseRange.BundleCycles
