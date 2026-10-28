import OAI.AlgebraicTopology.Cohomology.Singular.Functor

/-! # Ordinary Homeomorph Cohomology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OrdinaryHomeomorphCohomology.Constructions

noncomputable section

/-! The actual two inverse pullbacks associated to a topological isomorphism. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.Functor

def rationalCohomologyIsoOfTopologicalIso {X Y : TopCat.{0}} (e : X ≅ Y) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y n ≅ AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n where
  hom := AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) e.hom n
  inv := AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) e.inv n
  hom_inv_id := by
    rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp, e.inv_hom_id, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id]
  inv_hom_id := by
    rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp, e.hom_inv_id, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id]

theorem rationalCohomologyPullback_isIso {X Y : TopCat.{0}} (e : X ≅ Y) (n : ℕ) :
    IsIso (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) e.hom n) :=
  (rationalCohomologyIsoOfTopologicalIso e n).isIso_hom

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OrdinaryHomeomorphCohomology.Constructions
