import OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointCanonical
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree

/-! # Canonical Point Projection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalPointProjection.Constructions

noncomputable section

/-! A canonically oriented point above the base origin integrates to the original base normal class. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointCanonical.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartComplexManifold.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.PointProjection.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem pointProductBound (p d : ℕ) (x : Fin d → ℂ) (K : Set (Fin d → ℂ)) (hx : x ∈ K) :
    (({0} : Set (Fin p → ℂ)) ×ˢ {x}) ⊆ ({0} : Set (Fin p → ℂ)) ×ˢ K :=
  fun _ hz => ⟨hz.1, (Set.mem_singleton_iff.mp hz.2).symm ▸ hx⟩

theorem canonicalPoint_project (p d : ℕ) (x : Fin d → ℂ) (K : Set (Fin d → ℂ))
    (hK : IsCompact K) (hx : x ∈ K)
    (e : ((Fin p → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (p + d) → ℂ)) :
    letI := SingleChartComplexManifold.Constructions.coordinateChartedSpace (p + d) e.toHomeomorph
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of (Fin p → ℂ)) {0} K hK (({0} : Set (Fin p → ℂ)) ×ˢ {x})
      (pointProductBound p d x K hx) (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (𝟙 (TopCat.of ((Fin p → ℂ) × (Fin d → ℂ)))) (Product.PointCanonical.Constructions.Class.productPointComplement p d x)
        (2 * (p + d)) (CanonicalLocalDual.Constructions.canonicalLocalDual (p + d) (0, x))) = Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p := by
  let := SingleChartComplexManifold.Constructions.coordinateChartedSpace (p + d) e.toHomeomorph
  refine (congrArg (Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of (Fin p → ℂ)) {0} K hK
    (({0} : Set (Fin p → ℂ)) ×ˢ {x}) (pointProductBound p d x K hx)
    (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm)
    (Product.PointCanonical.Constructions.Class.productPointClass_canonical p d x e)).symm.trans ?_
  refine (Supported.ProjectionDegree.Constructions.projectAt_cast d (TopCat.of (Fin p → ℂ)) {0} K hK
    (({0} : Set (Fin p → ℂ)) ×ˢ {x}) (pointProductBound p d x K hx)
    (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm _).trans ?_
  exact Supported.PointProjection.Constructions.projectSupported_point d (TopCat.of (Fin p → ℂ)) {0} isClosed_singleton
    K hK x hx (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalPointProjection.Constructions
