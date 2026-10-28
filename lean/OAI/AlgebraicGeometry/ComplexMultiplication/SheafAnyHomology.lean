import OAI.Analysis.DifferentialForms.Manifold.ComplexSheafHomology

/-! # Sheaf Any Homology -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SheafAnyHomology

/-! # Homology for every inherited zero-morphism structure on actual complex sheaves -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- The unique zero-morphism structure lets every actual sheaf complex use abelian homology. -/
instance complexSheaves_haveHomology_anyZero (M : TopCat.{0})
    (z : HasZeroMorphisms (TopCat.Sheaf (ModuleCat.{0} ℂ) M)) :
    @CategoryWithHomology (TopCat.Sheaf (ModuleCat.{0} ℂ) M) inferInstance z := by
  convert (CategoryTheory.categoryWithHomology_of_abelian
    (C := TopCat.Sheaf (ModuleCat.{0} ℂ) M)) using 1
  exact Subsingleton.elim _ _

end OAI.AlgebraicGeometry.ComplexMultiplication.SheafAnyHomology
