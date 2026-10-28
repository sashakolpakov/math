import OAI.AlgebraicGeometry.Comparison.Betti.Finite.ProductCohomology
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-! # Coproduct Cohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.CoproductCohomology.Cech

noncomputable section

/-! Finite coproducts of cohomologically acyclic additive sheaves are acyclic. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

theorem finiteCoproduct_cohomology_subsingleton {X : TopCat.{u}} {ι : Type u} [Finite ι]
    (F : ι → Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [HasCoproduct F] (n : ℕ)
    (hF : ∀ i, Subsingleton (Sheaf.H (F i) n)) :
    Subsingleton (Sheaf.H (∐ F) n) := by
  let H := Sheaf.functorH (Opens.grothendieckTopology X) n
  have hzero (i : ι) : IsZero (H.obj (F i)) := by
    have : Subsingleton (H.obj (F i)) := hF i
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hsum : IsZero (∐ fun i => H.obj (F i)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Sigma.hom_ext
    intro i
    exact (hzero i).eq_of_src _ _
  exact AddCommGrpCat.subsingleton_of_isZero
    (hsum.of_iso (PreservesCoproduct.iso H F))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.CoproductCohomology.Cech
