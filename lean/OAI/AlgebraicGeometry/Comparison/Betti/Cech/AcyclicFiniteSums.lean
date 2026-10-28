import OAI.AlgebraicGeometry.Comparison.Betti.Cech.AcyclicShortExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Acyclic Finite Sums -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.AcyclicFiniteSums

noncomputable section

/-! Finite sums preserve actual acyclicity on every Čech intersection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

theorem additiveCoproduct_isZero {ι : Type} (F : ι → AddCommGrpCat.{0})
    (hF : ∀ i, IsZero (F i)) : IsZero (∐ F) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Sigma.hom_ext
  intro i
  exact (hF i).eq_of_src _ _

theorem cechIntersectionsAcyclic_finiteCoproduct {X : TopCat.{0}} {ι κ : Type} [Fintype κ]
    (U : ι → Opens X) (F : κ → TopCat.Sheaf AddCommGrpCat.{0} X)
    (hF : ∀ i, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U (F i)) :
    SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U (∐ F) := by
  intro p t q
  let V : Opens X := ∏ᶜ fun k : Fin (p + 1) => U (t k)
  let R := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0} V.isOpenEmbedding
  let H := Sheaf.functorH.{0} (Opens.grothendieckTopology V) (q + 1)
  let G : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} := R ⋙ H
  let : Abelian (TopCat.Sheaf AddCommGrpCat.{0} X) := inferInstance
  let : R.Additive := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict_additive V.isOpenEmbedding
  let : H.Additive := inferInstanceAs ((Sheaf.functorH.{0} (Opens.grothendieckTopology V) (q + 1)).Additive)
  let : G.Additive := by
    constructor
    intro A B f g
    exact (congrArg H.map (R.map_add (f := f) (g := g))).trans
      (H.map_add (f := R.map f) (g := R.map g))
  let : PreservesFiniteCoproducts G := inferInstance
  have hG (i : κ) : IsZero (G.obj (F i)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr (hF i p t q)
  have hZ := additiveCoproduct_isZero (fun i => G.obj (F i)) hG
  exact AddCommGrpCat.isZero_iff_subsingleton.mp (hZ.of_iso (PreservesCoproduct.iso G F))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.AcyclicFiniteSums
