import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry

/-! # Inducing Formula Field Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaFieldSymmetry

noncomputable section

/-! Proper group geometry supplies the detecting diagonal for the actual inducing-line formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)
  (formula : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])

/-- The formula symmetry follows from ordinary proper smooth connected group hypotheses;
no diagonal detection or formula-equivariance assumption is supplied. -/
theorem formula_equivariant
    (hσ : (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso σ = AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison A Q) :
    (Scheme.Modules.pullback (β_ A A).hom.left).mapIso (InducingFormulaSymmetry.regrouped A Q L formula) ≪≫ InducingFormulaSymmetry.targetSymmetry A L =
      InducingFormulaSymmetry.sourceSymmetry A Q L σ ≪≫ InducingFormulaSymmetry.regrouped A Q L formula := by
  have : IsIso (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left.appTop := AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_appTop_isIso A
  exact InducingFormulaSymmetry.formula_equivariant A Q L σ formula hσ

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaFieldSymmetry
