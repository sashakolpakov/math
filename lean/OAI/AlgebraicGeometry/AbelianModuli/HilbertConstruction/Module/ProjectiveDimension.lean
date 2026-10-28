import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.CategoryProjectives
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.DimensionBasic

/-! # Projective Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ProjectiveDimension

open _root_.CategoryTheory
universe v u
variable {R : Type u} [Ring R] [Small.{v} R]

omit [Small.{v, u} R] in
lemma ModuleCat.projectiveDimension_eq_zero_of_projective (M : ModuleCat.{v} R)
    [Nontrivial M] [Projective M] : HilbertConstruction.Projective.DimensionBasic.projectiveDimension M = 0 := by
  simpa [HilbertConstruction.Projective.DimensionBasic.projectiveDimension_eq_zero_iff, ModuleCat.isZero_iff_subsingleton,
    not_subsingleton_iff_nontrivial] using And.intro ‹Projective M› ‹Nontrivial M›

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ProjectiveDimension
