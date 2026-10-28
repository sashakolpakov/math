import OAI.AlgebraicGeometry.Comparison.Betti.Affine.FormPushforwardAcyclic
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.ProductCohomology
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.CechForms
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechFunctor

/-! # Affine Cech Acyclic -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.AffineCechAcyclic

noncomputable section

/-! Each term of the actual finite affine Čech resolution of algebraic forms is acyclic. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))

include hU in
theorem finiteAffineCech_algebraicForms_term_acyclic (n p q : ℕ) :
    Subsingleton (Sheaf.H
      (((Betti.Sheaf.CechFunctor.sheafCechResolutionFunctor U).obj (Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf X n)).X p)
      (q + 1)) := by
  have : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    infer_instance
  change Subsingleton (Sheaf.H
    (∏ᶜ SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermFactor (Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf X n) U p) (q + 1))
  apply ProductCohomology.Cech.finiteProduct_cohomology_subsingleton
  intro i
  change Fin (p + 1) → ι at i
  exact Affine.FormPushforwardAcyclic.affineOpen_algebraicFormPushforward_acyclic X
    (∏ᶜ fun k : Fin (p + 1) => U (i k))
    (SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU p i) n q

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.AffineCechAcyclic
