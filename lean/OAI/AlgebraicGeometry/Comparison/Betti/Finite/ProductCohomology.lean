import OAI.AlgebraicGeometry.SheafCohomology.Cech.Compat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Product Cohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.ProductCohomology.Cech

noncomputable section

/-! Finite products of cohomologically acyclic additive sheaves are acyclic. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

theorem finiteProduct_cohomology_subsingleton {X : TopCat.{u}} {ι : Type u} [Finite ι]
    (F : ι → TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (hF : ∀ i, Subsingleton (Sheaf.H (F i) n)) :
    Subsingleton (Sheaf.H (∏ᶜ F) n) := by
  let H := Sheaf.functorH (Opens.grothendieckTopology X) n
  have hzero (i : ι) : IsZero (H.obj (F i)) := by
    have : Subsingleton (H.obj (F i)) := hF i
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hprod : IsZero (∏ᶜ fun i => H.obj (F i)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Pi.hom_ext
    intro i
    exact (hzero i).eq_of_tgt _ _
  exact AddCommGrpCat.subsingleton_of_isZero
    (hprod.of_iso (PreservesProduct.iso H F))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.ProductCohomology.Cech
