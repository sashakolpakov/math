import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentCoordinates
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections

/-! # Tangent Normal Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TangentNormalRestriction.Constructions

noncomputable section

/-! Actual global supported classes retain their local normalization after
a norm-preserving complex change of tangent coordinates. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections.Cycles

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentCoordinates.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
  {f : M → N} {x : M} {p : ℕ} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
  (e : E ≃L[ℂ] G) (he : ∀ v, ‖e v‖ = ‖v‖)

theorem tangentCoordinates_normalizedRestriction
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ (2 * p))
    (ha : Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ P.openNeighborhood (2 * p) a = P.rationalClassFin) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (NormalPair.TangentCoordinates.Constructions.tangentCoordinateNormalPair P e he).openNeighborhood (2 * p) a =
        (NormalPair.TangentCoordinates.Constructions.tangentCoordinateNormalPair P e he).rationalClassFin := by
  have hc : NormalPair.TangentCoordinates.Constructions.tangentCoordinateNeighborhoodMap P e he ≫
      Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood =
      Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (NormalPair.TangentCoordinates.Constructions.tangentCoordinateNormalPair P e he).neighborhood := by
    ext z
    rfl
  have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (NormalPair.TangentCoordinates.Constructions.tangentCoordinateNeighborhoodMap P e he) (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood)
    (NormalPair.TangentCoordinates.Constructions.tangentCoordinateNeighborhoodMap_mapsTo P e he)
    (show Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood) P.relativeComplement
      (Set.range f)ᶜ from fun _ hz => hz) (2 * p)
  simp only [hc] at h
  have hval := ConcreteCategory.congr_hom h a
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.TangentCoordinates.Constructions.tangentCoordinateNeighborhoodMap P e he)
    (NormalPair.TangentCoordinates.Constructions.tangentCoordinateNeighborhoodMap_mapsTo P e he) (2 * p)
    (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ P.openNeighborhood (2 * p) a) =
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (NormalPair.TangentCoordinates.Constructions.tangentCoordinateNormalPair P e he).openNeighborhood (2 * p) a at hval
  rw [ha] at hval
  exact hval.symm.trans (NormalPair.TangentCoordinates.Constructions.tangentCoordinateNormalClass e he P)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TangentNormalRestriction.Constructions
