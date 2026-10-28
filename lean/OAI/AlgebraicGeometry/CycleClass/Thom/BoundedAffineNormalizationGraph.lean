import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.OpenRange
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.AffineSchemeGraph
import OAI.AlgebraicGeometry.CycleClass.Thom.Proper.GraphOpenBaseBound

/-! # Bounded Affine Normalization Graph -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.BoundedAffineNormalizationGraph.Constructions

noncomputable section

/-! Every point of an ambient affine open in the smooth-normalization base has a genuine bounded polynomial normalization graph over an ambient analytic neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.OpenRange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions.Open
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Proper.GraphOpenBaseBound.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.GraphEmbedding.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) (hB : B ≤ Normalization.AmbientMap.Constructions.ambientOpen V D.val) (hA : IsAffineOpen B)

theorem exists_bounded_affine_normalization_graph (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B)) :
    letI : IsAffine (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left := hA
    letI : IsAffine (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left := Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource_affine D B hA
    ∃ (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left, ⊤))
      (U : Opens V.analyticSpace) (K : Set (Fin d → ℂ)),
      Function.Surjective f ∧ IsClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B) f).left ∧
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) x ∈ U ∧
      (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)) ∧ IsCompact K ∧
      Topology.IsClosedEmbedding (GraphBaseRestriction.Constructions.restrictedGraph (Normalization.GenericFibers.Constructions.Open.openBase D (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB))
        (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (U : Set V.analyticSpace)) ∧
      ∀ y, Normalization.GenericFibers.Constructions.Open.openBase D (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) y ∈ U → Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K := by
  let : IsAffine (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left := Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource_affine D B hA
  let : IsAffine (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left := hA
  let : LocallyOfFiniteType (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).hom := inferInstanceAs (LocallyOfFiniteType (B.ι ≫ V.structureMap))
  let : LocallyOfFiniteType (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).hom := by
    rw [← (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B).w]
    infer_instance
  let : LocallyCompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B)) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.affineSchemePoints_locallyCompact (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B)
  obtain ⟨d, f, hf, hscheme⟩ := Affine.SchemeGraph.Constructions.exists_globalGraphSchemeMap (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B)
  obtain ⟨U, K, hx, hU, hK, hb⟩ := Proper.GraphOpenBaseBound.Constructions.exists_ambient_local_compact_bound
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B))
    (Affine.SchemeIntegralProper.Constructions.isProperMap_affine_integral (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B))
    (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_continuous f) x
  have hcont : Continuous (Normalization.GenericFibers.Constructions.Open.openBase D (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB)) :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V D.val)).comp
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB))
  have hc := Closed.GraphEmbedding.Constructions.graph_closedEmbedding (Normalization.GenericFibers.Constructions.Open.openBase D (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB)) hcont
    (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_closedEmbedding f hf)
  refine ⟨d, f, U, K, hf, hscheme, hx, hU, hK,
    GraphBaseRestriction.Constructions.restrictedGraph_closedEmbedding (Normalization.GenericFibers.Constructions.Open.openBase D (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB)) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) U hc, ?_⟩
  intro y hy
  apply hb y
  exact (congrArg (fun z : V.analyticSpace => z ∈ U)
    (congrFun (NormalizationAffine.OpenRange.Constructions.affine_openBase_eq D B hB) y)).mp hy

end

end OAI.AlgebraicGeometry.CycleClass.Thom.BoundedAffineNormalizationGraph.Constructions
