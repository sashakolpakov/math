import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.TranslationCommutation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.OriginPathDefectSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaFieldSymmetry

/-! # Translation Defect Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.TranslationDefectSymmetry

noncomputable section

/-! Isotropy proves symmetry of the actual regular translation defect, without assuming that symmetry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry

variable {k : Type u} [Field k] [IsAlgClosed k] {H A : Over (Spec (.of k))}
  [GrpObj H] [IsCommMonObj H] [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] [IsIntegral A.left]
  (i : H ⟶ A) [IsMonHom i] (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)
  (u : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule H.left ≅ Line.Fibers.fiber L i)
  (o : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅ Line.Fibers.fiber L η[A])

include o

/-- Actual scheme-valued isotropy and the inducing formula force the regular defect to be symmetric. -/
theorem value_symmetric
    (he : (Scheme.Modules.pullback (β_ A A).hom.left).mapIso (InducingFormulaSymmetry.regrouped A Q L e) ≪≫ InducingFormulaSymmetry.targetSymmetry A L =
      InducingFormulaSymmetry.sourceSymmetry A Q L σ ≪≫ InducingFormulaSymmetry.regrouped A Q L e)
    (hi : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ H), Kernel.IntersectionFrames.obstruction i i (Line.Comparison.Bundle.fromShared Q) s
      (Symmetric.KernelTrivialization.secondFrame i (Line.Comparison.Bundle.fromShared Q) s σ) a b = 1)
    {T : Over (Spec (.of k))} (a b : T ⟶ H) :
    Subgroup.DefectParameters.value i L (FramedSubgroupInducingProduct.translationIso i Q L e s u) a b =
      Subgroup.DefectParameters.value i L (FramedSubgroupInducingProduct.translationIso i Q L e s u) b a :=
  OriginPathDefectSymmetry.value_symmetric i L (FramedSubgroupInducingProduct.translationIso i Q L e s u)
    (fun _T a b z hab hba => TranslationCommutation.paths_commute i Q L e s σ u o he hi a b z hab hba) a b

/-- Proper group rigidity constructs the required formula equivariance from diagonal normalization. -/
theorem value_symmetric_of_diagonal
    (hσ : (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso σ = AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison A Q)
    (hi : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ H), Kernel.IntersectionFrames.obstruction i i (Line.Comparison.Bundle.fromShared Q) s
      (Symmetric.KernelTrivialization.secondFrame i (Line.Comparison.Bundle.fromShared Q) s σ) a b = 1)
    {T : Over (Spec (.of k))} (a b : T ⟶ H) :
    Subgroup.DefectParameters.value i L (FramedSubgroupInducingProduct.translationIso i Q L e s u) a b =
      Subgroup.DefectParameters.value i L (FramedSubgroupInducingProduct.translationIso i Q L e s u) b a :=
  value_symmetric i Q L e s σ u o (InducingFormulaFieldSymmetry.formula_equivariant A Q L σ e hσ) hi a b

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.TranslationDefectSymmetry
