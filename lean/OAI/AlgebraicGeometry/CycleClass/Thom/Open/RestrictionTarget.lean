import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections

/-! # Restriction Target -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionTarget.Constructions

noncomputable section

/-! Rewriting only the removed subset of an actual open pair restriction. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections.Cycles

variable (T : TopCat.{0}) (B : Set T) (U : Opens T) (A : Set U)
  (h : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace B U = A)

include h in
theorem openRestrictionMapsTo : Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion T (U : Set T)) A B := by
  intro y hy
  change y ∈ AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace B U
  exact (congrArg (fun S : Set U => y ∈ S) h).mpr hy

theorem openRestriction_change_target (n : ℕ) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T B U n ≫
      eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) S n) h) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion T (U : Set T))
      (openRestrictionMapsTo T B U A h) n := by
  subst A
  exact Category.comp_id _

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionTarget.Constructions
