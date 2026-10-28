import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaFieldSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Symmetry

/-! # Formula Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.FormulaSymmetry

noncomputable section

/-! The canonical symmetry constructed from the original polarization respects every actual inducing-line formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (ell : A.scheme ⟶ D.abelian.scheme) [IsMonHom ell] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
  (hformula : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) ell).sheaf (L.pullback (fst A.scheme A.scheme).left).sheaf)
    (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)) (n : ℕ)
  (M : Line.Bundles.LineBundle A.scheme.left)
  (formula : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)).sheaf (Line.Fibers.fiber M (fst A.scheme A.scheme)))
    (Line.Fibers.fiber M (snd A.scheme A.scheme)) ≅ Line.Fibers.fiber M μ[A.scheme])

omit [IsMonHom ell] in
/-- No symmetry of the inducing formula is assumed: it follows from the original polarization's
canonical diagonal-normalized Poincare symmetry and proper group geometry. -/
theorem formula_equivariant :
    (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).mapIso
        (InducingFormulaSymmetry.regrouped A.scheme (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)) M formula) ≪≫ InducingFormulaSymmetry.targetSymmetry A.scheme M =
      InducingFormulaSymmetry.sourceSymmetry A.scheme (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)) M
        (Symmetry.ReferencePoincare.symmetry D ell L hformula n) ≪≫
          InducingFormulaSymmetry.regrouped A.scheme (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)) M formula :=
  InducingFormulaFieldSymmetry.formula_equivariant A.scheme (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)) M
    (Symmetry.ReferencePoincare.symmetry D ell L hformula n) formula
    (Symmetry.ReferencePoincare.symmetry_diagonal D ell L hformula n)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.FormulaSymmetry
