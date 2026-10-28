import OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalPointProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SupportEnlargement
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PointCohomology

/-! # Point Projection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PointProjection.Constructions

noncomputable section

/-! Supported projection sums the canonical point coefficients in a finite fiber over the base origin. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalPointProjection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointCanonical.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartComplexManifold.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SupportEnlargement.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CompactPointIntegration.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PointCohomology.Constructions.LocalCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem singletonBound (p d : ℕ) (x : Fin d → ℂ) (K : Set (Fin d → ℂ)) (hx : x ∈ K) :
    ({(0, x)} : Set ((Fin p → ℂ) × (Fin d → ℂ))) ⊆ ({0} : Set (Fin p → ℂ)) ×ˢ K := by
  rintro z rfl
  exact ⟨rfl, hx⟩

theorem singleton_project (p d : ℕ) (x : Fin d → ℂ) (K : Set (Fin d → ℂ))
    (hK : IsCompact K) (hx : x ∈ K)
    (e : ((Fin p → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (p + d) → ℂ)) :
    letI := SingleChartComplexManifold.Constructions.coordinateChartedSpace (p + d) e.toHomeomorph
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of (Fin p → ℂ)) {0} K hK {(0, x)}
      (singletonBound p d x K hx) (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (CanonicalLocalDual.Constructions.canonicalLocalDual (p + d) (0, x)) = Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p := by
  let := SingleChartComplexManifold.Constructions.coordinateChartedSpace (p + d) e.toHomeomorph
  have hinc : ({(0, x)} : Set ((Fin p → ℂ) × (Fin d → ℂ))) ⊆ {0} ×ˢ {x} := by
    rintro z rfl
    exact ⟨rfl, rfl⟩
  refine (Projection.SupportEnlargement.Constructions.projectAt_support d (TopCat.of (Fin p → ℂ)) {0} K hK {(0, x)} ({0} ×ˢ {x})
    (singletonBound p d x K hx) (CanonicalPointProjection.Constructions.pointProductBound p d x K hx) hinc
    (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm (CanonicalLocalDual.Constructions.canonicalLocalDual (p + d) (0, x))).symm.trans ?_
  exact CanonicalPointProjection.Constructions.canonicalPoint_project p d x K hK hx e

theorem finitePoint_project (p d : ℕ) (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (T : Set ((Fin p → ℂ) × (Fin d → ℂ))) (hT : T ⊆ {0} ×ˢ K)
    (z : T)
    (e : ((Fin p → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (p + d) → ℂ)) :
    letI := SingleChartComplexManifold.Constructions.coordinateChartedSpace (p + d) e.toHomeomorph
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of (Fin p → ℂ)) {0} K hK T hT
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (CompactPointIntegration.Constructions.compactPointClass (p + d) T z.val z.property) = Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p := by
  let := SingleChartComplexManifold.Constructions.coordinateChartedSpace (p + d) e.toHomeomorph
  have hz0 : z.val.1 = 0 := (hT z.property).1
  have hzK : z.val.2 ∈ K := (hT z.property).2
  have hzx : z.val = (0, z.val.2) := Prod.ext hz0 rfl
  have hsingle : {z.val} ⊆ T := Set.singleton_subset_iff.mpr z.property
  have hsbound : {z.val} ⊆ ({0} : Set (Fin p → ℂ)) ×ˢ K := hsingle.trans hT
  refine (Projection.SupportEnlargement.Constructions.projectAt_support d (TopCat.of (Fin p → ℂ)) {0} K hK {z.val} T hsbound hT hsingle
    (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm (CanonicalLocalDual.Constructions.canonicalLocalDual (p + d) z.val)).trans ?_
  generalize hz : z.val = w at *
  rcases w with ⟨a, b⟩
  change a = 0 at hz0
  subst a
  exact singleton_project p d b K hK hzK e

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PointProjection.Constructions
