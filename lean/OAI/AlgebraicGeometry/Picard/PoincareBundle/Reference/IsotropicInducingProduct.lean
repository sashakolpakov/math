import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.InducingProductSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.FormulaSymmetry

/-! # Isotropic Inducing Product -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.IsotropicInducingProduct

noncomputable section

/-! Isotropy gives the inducing-product symmetry for the canonical line of the original polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames

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

/-- The canonical original symmetry and scheme-valued isotropy force symmetry of the actual
invertible inducing-line product; no formula-equivariance hypothesis is supplied. -/
theorem product_equivariant
    (hi : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ H),
      Kernel.IntersectionFrames.obstruction i i (Line.Comparison.Bundle.fromShared (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n))) s
        (Symmetric.KernelTrivialization.secondFrame i (Line.Comparison.Bundle.fromShared (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n))) s
          (Symmetry.ReferencePoincare.symmetry D ell L hformula n)) a b = 1) :
    (Scheme.Modules.pullback (β_ H H).hom.left).map
        (Isotropic.InducingProductSymmetry.product i (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)) M s formula) ≫
        (RestrictedLineEquivariance.symmetry (i ⊗ₘ i) (β_ A.scheme A.scheme).hom (β_ H H).hom
          (Kernel.IntersectionSymmetry.swap_square i) (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.targetLine A.scheme M))
          (InducingFormulaSymmetry.targetSymmetry A.scheme M)).hom =
      (RestrictedLineEquivariance.symmetry (i ⊗ₘ i) (β_ A.scheme A.scheme).hom (β_ H H).hom
          (Kernel.IntersectionSymmetry.swap_square i) (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A.scheme M))
          (ExternalTensorSymmetry.symmetry A.scheme M)).hom ≫
        Isotropic.InducingProductSymmetry.product i (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)) M s formula :=
  Isotropic.InducingProductSymmetry.equivariant i (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)) M s
    (Symmetry.ReferencePoincare.symmetry D ell L hformula n) formula
    (FormulaSymmetry.formula_equivariant D ell L hformula n M formula) hi

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.IsotropicInducingProduct
