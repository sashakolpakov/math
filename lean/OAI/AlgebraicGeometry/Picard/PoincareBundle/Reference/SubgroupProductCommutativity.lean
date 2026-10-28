import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.SubgroupFiberCommutativity
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.FormulaSymmetry

/-! # Subgroup Product Commutativity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.SubgroupProductCommutativity

noncomputable section

/-! Isotropy for the original polarization gives actual commutative subgroup products on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (ell : A.scheme ⟶ D.abelian.scheme) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
  (hformula : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) ell).sheaf (L.pullback (fst A.scheme A.scheme).left).sheaf)
    (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)) (n : ℕ)
  {H : Over (Spec (.of k))} (i : H ⟶ A.scheme)
  (M : Line.Bundles.LineBundle A.scheme.left)
  (formula : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)).sheaf (Line.Fibers.fiber M (fst A.scheme A.scheme)))
    (Line.Fibers.fiber M (snd A.scheme A.scheme)) ≅ Line.Fibers.fiber M μ[A.scheme])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A.scheme).left ≅
    (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A.scheme).left).obj (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)).sheaf)

/-- The original formula, its constructed canonical symmetry, and scheme-valued isotropy force
commutativity of the actual product used to define subgroup translation. -/
theorem commutative
    (hi : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ H),
      Kernel.IntersectionFrames.obstruction i i (Line.Comparison.Bundle.fromShared (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n))) s
        (Symmetric.KernelTrivialization.secondFrame i (Line.Comparison.Bundle.fromShared (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n))) s
          (Symmetry.ReferencePoincare.symmetry D ell L hformula n)) a b = 1)
    {T : Over (Spec (.of k))} (a b : T ⟶ H) (z : T ⟶ A.scheme)
    (hab : (a ≫ i) * (b ≫ i) = z) (hba : (b ≫ i) * (a ≫ i) = z)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber M (a ≫ i), U)) (v : Γ(Line.Fibers.fiber M (b ≫ i), U)) :
    (FramedSubgroupFiberProducts.atPoint i (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)) M formula s
        a (b ≫ i) z hab).app U m v =
      (FramedSubgroupFiberProducts.atPoint i (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)) M formula s
        b (a ≫ i) z hba).app U v m :=
  Isotropic.SubgroupFiberCommutativity.commutative i (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)) M s
    (Symmetry.ReferencePoincare.symmetry D ell L hformula n) formula
    (FormulaSymmetry.formula_equivariant D ell L hformula n M formula) hi a b z hab hba U m v

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.SubgroupProductCommutativity
