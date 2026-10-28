import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.AffineAcyclicity
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Comparison

/-! # Cech Forms -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.CechForms

noncomputable section

/-! Affine covers compute positive sheaf cohomology of the original algebraic forms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsSeparated X.hom]
  {ι : Type} (U : ι → X.left.Opens) (hUaff : ∀ i, IsAffineOpen (U i))

include hUaff in
theorem algebraicForm_affineCech_acyclic (n : ℕ) :
    SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U (ExteriorAcyclicity.algebraicFormAdditiveSheaf X n) := by
  have : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    infer_instance
  intro p i q
  exact Betti.Smooth.AffineAcyclicity.smooth_affineOpen_algebraicForms_acyclic X
    (∏ᶜ fun k : Fin (p + 1) => U (i k))
    (SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hUaff p i) n q

def algebraicForm_affineCechCohomologyIso (hU : IsOpenCover U) (n q : ℕ) :
    ((cechComplexFunctor U).obj (ExteriorAcyclicity.algebraicFormAdditiveSheaf X n).obj).homology (q + 1) ≅
      (Sheaf.functorH (Opens.grothendieckTopology X.left) (q + 1)).obj
        (ExteriorAcyclicity.algebraicFormAdditiveSheaf X n) :=
  SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections U (ExteriorAcyclicity.algebraicFormAdditiveSheaf X n)
    hU.iSup_eq_top (algebraicForm_affineCech_acyclic X U hUaff n) q

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.CechForms
