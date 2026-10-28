import OAI.Analysis.DifferentialForms.Manifold.SmoothFormD
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.Abelian

/-! # Complex Sheaf Category -/

namespace OAI.Analysis.DifferentialForms.Manifold.ComplexSheafCategory

noncomputable section

/-!
# Complex-module sheaves in arbitrary ambient universes

These are specializations of mathlib's actual limit and filtered-colimit
constructions. The scalar field remains the ordinary complex numbers while
the module carrier and base space may lie in a larger universe.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

/-- Complex modules admit limits for diagrams in their carrier universe. -/
instance complexModules_haveLimits : HasLimitsOfSize.{u,u} (ModuleCat.{u,0} ℂ) :=
  ModuleCat.hasLimitsOfSize.{u,u,u,0}

/-- The actual filtered colimit of complex modules has the usual underlying
filtered colimit of abelian groups, with no universe equality for the scalars. -/
instance complexModules_forget₂_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (ModuleCat.{u,0} ℂ) AddCommGrpCat.{u}) where
  preserves_filtered_colimits _ _ _ :=
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone
          (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ (ModuleCat.{u,0} ℂ) AddCommGrpCat.{u})) }

/-- Forgetting a complex module preserves filtered colimits in its universe. -/
instance complexModules_forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget (ModuleCat.{u,0} ℂ)) :=
  Limits.comp_preservesFilteredColimits (forget₂ (ModuleCat.{u,0} ℂ) AddCommGrpCat.{u})
    (forget AddCommGrpCat.{u})

/-- Sheafification exists for actual complex-module presheaves on any such space. -/
theorem complexSheaves_haveSheafify (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u,0} ℂ) := by
  infer_instance

/-- The corresponding category of actual complex-module sheaves is abelian. -/
abbrev complexSheaves_abelian (X : TopCat.{u}) :
    Abelian (TopCat.Sheaf (ModuleCat.{u,0} ℂ) X) := by
  infer_instance

end

end OAI.Analysis.DifferentialForms.Manifold.ComplexSheafCategory
