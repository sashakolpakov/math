import OAI.AlgebraicGeometry.Comparison.Betti.Finite.CoproductCohomology
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Topology.Sheaves.Sheafify
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalDiagonal

/-! # Total Cohomology Acyclic -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TotalCohomologyAcyclic.Cech

noncomputable section

/-! Finite diagonals preserve termwise sheaf-cohomology vanishing in a total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex₂

variable {X : TopCat.{0}}

theorem totalTerm_cohomology_subsingleton
    (K : HomologicalComplex₂
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) (.up ℕ) (.up ℕ))
    [K.HasTotal (.up ℕ)]
    (n q : ℕ) (hK : ∀ a b, Subsingleton (Sheaf.H.{0} ((K.X a).X b) q)) :
    Subsingleton (Sheaf.H.{0} ((K.total (.up ℕ)).X n) q) := by
  have : Finite ((ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {n}) := by
    change Finite {p : ℕ × ℕ // p.1 + p.2 = n}
    exact Betti.Finite.TotalDiagonal.finiteTotalDiagonal n
  exact Betti.Finite.CoproductCohomology.Cech.finiteCoproduct_cohomology_subsingleton
    (K.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n) q
    (fun p => hK p.val.1 p.val.2)

end

end OAI.AlgebraicGeometry.Comparison.Betti.TotalCohomologyAcyclic.Cech
