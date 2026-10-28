import OAI.Analysis.DifferentialForms.Manifold.ComplexSheafCategory
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # Complex Sheaf Homology -/

namespace OAI.Analysis.DifferentialForms.Manifold.ComplexSheafHomology

/-!
# Homology in the existing complex-module sheaf category

The explicit pointwise additive structure used by the form sheaves and the
one furnished by the abelian-category construction determine the same zero
morphisms. Transporting along their proved uniqueness exposes categorical
homology for complexes constructed with the former structure.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

/-- Actual complex-module sheaf complexes have categorical homology. -/
instance complexSheaves_haveHomology (X : TopCat.{u}) :
    CategoryWithHomology (TopCat.Sheaf (ModuleCat.{u} ℂ) X) := by
  convert (CategoryTheory.categoryWithHomology_of_abelian
    (C := TopCat.Sheaf (ModuleCat.{u} ℂ) X)) using 1
  exact Subsingleton.elim _ _

end OAI.Analysis.DifferentialForms.Manifold.ComplexSheafHomology
