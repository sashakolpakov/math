import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Cech
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.CechForms
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.AdditiveComplexExtension

/-! # Godement Cech Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.GodementCechAcyclicity

noncomputable section

/-! The original algebraic de Rham complex satisfies the termwise acyclicity needed by the Godement–Čech comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsSeparated X.hom]
  {ι : Type} (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))

include hU in
theorem algebraicGodementCechIntersectionsAcyclic (r : ℕ) :
    SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := TopCat.of X.left) U
      ((Complex.SheafForget.Flasque.sheafForget (TopCat.of X.left)).obj ((Sheaves.algebraicDeRhamSheafComplex X).X r)) :=
  Affine.CechForms.algebraicForm_affineCech_acyclic X U hU r

include hU in
theorem algebraicGodementCechTotalMap_quasiIso [Finite ι] :
    QuasiIso (Godement.Cech.godementCechTotalMap U (Sheaves.algebraicDeRhamSheafComplex X)) :=
  Godement.Cech.godementCechTotalMap_quasiIso U (Sheaves.algebraicDeRhamSheafComplex X)
    (algebraicGodementCechIntersectionsAcyclic X U hU)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.GodementCechAcyclicity
