import OAI.AlgebraicGeometry.CycleClass.Thom.EmbeddingChartPoint
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegreeNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PointProjection

/-! # Finite Point Projection -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Open.FinitePointProjection.Constructions.Product

/-! The actual canonical point in an open normal product projects to the open normal generator. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.EmbeddingComplexChart.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EmbeddingChartPoint.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartComplexManifold.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.LocalDualLocalInverse.Constructions.CanonicalNaturality
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegreeNaturality.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PointProjection.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {p d : ℕ} (U : Opens (Fin p → ℂ)) [Nonempty U]
  (e : ((Fin p → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (p + d) → ℂ))

@[instance_reducible]
def openProductCharted : ChartedSpace (Fin (p + d) → ℂ) (U × (Fin d → ℂ)) :=
  EmbeddingComplexChart.Constructions.embeddingChartedSpace (p + d) (ProductCoordinates.Constructions.flatOpenCoordinate U e) (ProductCoordinates.Constructions.flatOpenCoordinate_isOpenEmbedding U e)

omit [Nonempty U] in
theorem openSingletonBound (h0 : (0 : Fin p → ℂ) ∈ U) (x : Fin d → ℂ)
    (K : Set (Fin d → ℂ)) (hx : x ∈ K) :
    ({(⟨0, h0⟩, x)} : Set (U × (Fin d → ℂ))) ⊆ ({⟨0, h0⟩} : Set U) ×ˢ K := by
  rintro z rfl
  exact ⟨rfl, hx⟩

theorem openSingleton_project (h0 : (0 : Fin p → ℂ) ∈ U) (x : Fin d → ℂ)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K) (hx : x ∈ K) :
    letI := openProductCharted U e
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) {⟨0, h0⟩} K hK {(⟨0, h0⟩, x)}
      (openSingletonBound U h0 x K hx) (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (CanonicalLocalDual.Constructions.canonicalLocalDual (p + d) (M := U × (Fin d → ℂ)) ((⟨0, h0⟩ : U), x)) =
        HodgeConjecture.DegreeTwo.NestedOpenPointClass.Constructions.openOriginRelativeDualClass U h0 := by
  let := SingleChartComplexManifold.Constructions.coordinateChartedSpace (p + d) e.toHomeomorph
  let := openProductCharted U e
  let z : U × (Fin d → ℂ) := (⟨0, h0⟩, x)
  let J := HodgeConjecture.DegreeTwo.OpenNormal.Constructions.normalOpenProductInclusion U (TopCat.of (Fin d → ℂ))
  have hJ := HodgeConjecture.DegreeTwo.OpenNormal.Constructions.normalOpenProductInclusion_isOpenEmbedding U (TopCat.of (Fin d → ℂ))
  have hr := EmbeddingChartPoint.Constructions.Class.canonicalPoint_restriction (p + d) e.toHomeomorph J hJ z
  have hn := Supported.ProjectionDegreeNaturality.Constructions.projectAt_natural d (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin p → ℂ)) U)
    {⟨0, h0⟩} {0} {z} {(0, x)} K hK (openSingletonBound U h0 x K hx)
    (Finite.PointProjection.Constructions.singletonBound p d x K hx) (HodgeConjecture.DegreeTwo.NestedOpenPointClass.Constructions.openOrigin_mapsTo_complement U h0)
    (LocalDualLocalInverse.Constructions.CanonicalNaturality.injectivePunctureMapsTo J hJ.injective z) (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
    (CanonicalLocalDual.Constructions.canonicalLocalDual (p + d) (0, x))
  refine (congrArg (Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) {⟨0, h0⟩} K hK {z}
    (openSingletonBound U h0 x K hx) (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm)
    hr).symm.trans (hn.trans ?_)
  exact congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin p → ℂ)) U) (HodgeConjecture.DegreeTwo.NestedOpenPointClass.Constructions.openOrigin_mapsTo_complement U h0) (2 * p))
    (Finite.PointProjection.Constructions.singleton_project p d x K hK hx e)

end AlgebraicGeometry.CycleClass.Thom.Open.FinitePointProjection.Constructions.Product

namespace AlgebraicGeometry.CycleClass.Thom.Open.FinitePointProjection.Constructions

/-! The supported projection from an open normal product sums its actual finite local point coefficients. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.FinitePointProjection.Constructions.Product OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.EmbeddingComplexChart.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SupportEnlargement.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CompactPointIntegration.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PointCohomology.Constructions.LocalCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {p d : ℕ} (U : Opens (Fin p → ℂ)) [Nonempty U]
  (e : ((Fin p → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (p + d) → ℂ))

theorem openProductManifold :
    letI := Product.openProductCharted U e
    IsManifold 𝓘(ℂ, Fin (p + d) → ℂ) ω (U × (Fin d → ℂ)) :=
  EmbeddingComplexChart.Constructions.embeddingManifold (p + d) (ProductCoordinates.Constructions.flatOpenCoordinate U e) (ProductCoordinates.Constructions.flatOpenCoordinate_isOpenEmbedding U e)

theorem openPoint_project (h0 : (0 : Fin p → ℂ) ∈ U) (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (T : Set (U × (Fin d → ℂ))) (hT : T ⊆ {⟨0, h0⟩} ×ˢ K) (z : T) :
    letI := Product.openProductCharted U e
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) {⟨0, h0⟩} K hK T hT
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (CompactPointIntegration.Constructions.compactPointClass (p + d) T z.val z.property) = HodgeConjecture.DegreeTwo.NestedOpenPointClass.Constructions.openOriginRelativeDualClass U h0 := by
  let := Product.openProductCharted U e
  have hz0 : z.val.1 = ⟨0, h0⟩ := (hT z.property).1
  have hzK : z.val.2 ∈ K := (hT z.property).2
  have hsingle : {z.val} ⊆ T := Set.singleton_subset_iff.mpr z.property
  have hsbound : {z.val} ⊆ ({⟨0, h0⟩} : Set U) ×ˢ K := hsingle.trans hT
  refine (Projection.SupportEnlargement.Constructions.projectAt_support d (TopCat.of U) {⟨0, h0⟩} K hK {z.val} T hsbound hT hsingle
    (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm (CanonicalLocalDual.Constructions.canonicalLocalDual (p + d) z.val)).trans ?_
  generalize hz : z.val = w at *
  rcases w with ⟨a, b⟩
  change a = ⟨0, h0⟩ at hz0
  subst a
  exact Product.openSingleton_project U e h0 b K hK hzK

theorem openPointSum_project (h0 : (0 : Fin p → ℂ) ∈ U) (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (T : Set (U × (Fin d → ℂ))) [Fintype T] (hT : T ⊆ {⟨0, h0⟩} ×ˢ K) (w : T → ℚ) :
    letI := Product.openProductCharted U e
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) {⟨0, h0⟩} K hK T hT
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (∑ z : T, w z • CompactPointIntegration.Constructions.compactPointClass (p + d) T z.val z.property) =
        (∑ z : T, w z) • HodgeConjecture.DegreeTwo.NestedOpenPointClass.Constructions.openOriginRelativeDualClass U h0 := by
  let := Product.openProductCharted U e
  rw [map_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul, openPoint_project U e h0 K hK T hT z]

theorem openFiniteClass_project_of_local (h0 : (0 : Fin p → ℂ) ∈ U)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (T : Set (U × (Fin d → ℂ))) [Fintype T] (hT : T ⊆ {⟨0, h0⟩} ×ˢ K)
    (V : T → Opens (U × (Fin d → ℂ))) (hxV : ∀ x : T, x.val ∈ V x)
    (hVT : ∀ (x : T) (y : V x), y.val ∈ T → y.val = x.val)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U × (Fin d → ℂ))) Tᶜ (2 * (p + d)))
    (w : T → ℚ) :
    letI := Product.openProductCharted U e
    (∀ x : T, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (U × (Fin d → ℂ))) (V x : Set _))
      (Finite.PointCohomology.Constructions.LocalCoefficients.isolationMapsTo T (V x) ⟨x.val, hxV x⟩ (fun y hy => Subtype.ext (hVT x y hy)))
      (2 * (p + d)) a = w x • CanonicalLocalDual.Constructions.canonicalLocalDual (p + d) (⟨x.val, hxV x⟩ : V x)) →
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) {⟨0, h0⟩} K hK T hT
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm a =
        (∑ z : T, w z) • HodgeConjecture.DegreeTwo.NestedOpenPointClass.Constructions.openOriginRelativeDualClass U h0 := by
  let := Product.openProductCharted U e
  let := openProductManifold U e
  intro ha
  exact (congrArg (Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) {⟨0, h0⟩} K hK T hT
    (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm)
    (Finite.PointCohomology.Constructions.LocalCoefficients.cohomology_eq_sum_of_local (p + d) T V hxV hVT a w ha)).trans
    (openPointSum_project U e h0 K hK T hT w)

end AlgebraicGeometry.CycleClass.Thom.Open.FinitePointProjection.Constructions

end

end OAI
