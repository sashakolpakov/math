import OAI.AlgebraicGeometry.Picard.PoincareBundle.ExternalTensorSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FixedFiberSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.NormalizedRestriction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.RigidifiedFormulaEquivariance
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison

/-! # Inducing Formula Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry

noncomputable section

/-! An inducing-line formula respects the diagonal-normalized symmetry of its Poincare line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FixedRestriction

variable {S : Scheme.{u}} (A : Over S) (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left)
  (L : Line.Bundles.LineBundle A.left)

/-- The two copies of the inducing line on the product. -/
def factorLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left :=
  ((Line.Comparison.Bundle.toShared L).pullback (fst A A).left).tensor ((Line.Comparison.Bundle.toShared L).pullback (snd A A).left)

/-- Regroup the source as the Poincare line tensored with the external tensor square. -/
def sourceLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left := Q.tensor (factorLine A L)

variable (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)

def sourceSymmetry :
    (Scheme.Modules.pullback (β_ A A).hom.left).obj (sourceLine A Q L).sheaf ≅ (sourceLine A Q L).sheaf :=
  Tensor.LinePullback.pullbackIso (β_ A A).hom.left Q.sheaf (factorLine A L).sheaf Q.locallyTrivial (factorLine A L).locallyTrivial ≪≫
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr σ (ExternalTensorSymmetry.symmetry A L)

theorem source_normalized
    (hσ : (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso σ = AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison A Q) :
    (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso (sourceSymmetry A Q L σ) =
      Tensor.FixedRestriction.comparison (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left (β_ A A).hom.left
        (congrArg Over.Hom.left (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A)) (sourceLine A Q L).sheaf := by
  have hs : (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso σ =
      Tensor.FixedRestriction.comparison (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left (β_ A A).hom.left
        (congrArg Over.Hom.left (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A)) Q.sheaf := by
    simpa only [AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison, Tensor.FixedRestriction.comparison, NatIso.trans_app] using hσ
  have hr : (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso (ExternalTensorSymmetry.symmetry A L) =
      Tensor.FixedRestriction.comparison (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left (β_ A A).hom.left
        (congrArg Over.Hom.left (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A)) (factorLine A L).sheaf :=
    ExternalTensorSymmetry.diagonal A L
  exact Tensor.NormalizedRestriction.normalized_tensor (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left (β_ A A).hom.left
    (congrArg Over.Hom.left (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A)) Q.sheaf (factorLine A L).sheaf
    Q.locallyTrivial (factorLine A L).locallyTrivial σ (ExternalTensorSymmetry.symmetry A L)
    hs hr

variable [GrpObj A] [IsCommMonObj A]

def targetLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left := (Line.Comparison.Bundle.toShared L).pullback μ[A].left

def targetSymmetry :
    (Scheme.Modules.pullback (β_ A A).hom.left).obj (targetLine A L).sheaf ≅ (targetLine A L).sheaf :=
  Line.Fibers.fiberPullbackIso L (β_ A A).hom μ[A] μ[A] (IsCommMonObj.mul_comm A)

theorem target_normalized :
    (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso (targetSymmetry A L) =
      Tensor.FixedRestriction.comparison (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left (β_ A A).hom.left
        (congrArg Over.Hom.left (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A)) (targetLine A L).sheaf :=
  FixedFiberSymmetry.normalized L (β_ A A).hom (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A) (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A)
    μ[A] (IsCommMonObj.mul_comm A)

variable (formula : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])

def regrouped : (sourceLine A Q L).sheaf ≅ (targetLine A L).sheaf :=
  (Homomorphisms.TensorAssociativity.Construction.tensorModuleAssocIso Q.sheaf (Line.Fibers.fiber L (fst A A)) (Line.Fibers.fiber L (snd A A))).symm ≪≫ formula

/-- Rigidity forces compatibility of the actual inducing-line formula with the normalized symmetry. -/
theorem formula_equivariant [IsIso (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left.appTop]
    (hσ : (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso σ = AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison A Q) :
    (Scheme.Modules.pullback (β_ A A).hom.left).mapIso (regrouped A Q L formula) ≪≫ targetSymmetry A L =
      sourceSymmetry A Q L σ ≪≫ regrouped A Q L formula :=
  RigidifiedFormulaEquivariance.equivariance (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left (β_ A A).hom.left
    (congrArg Over.Hom.left (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A)) (sourceLine A Q L) (targetLine A L)
    (regrouped A Q L formula) (sourceSymmetry A Q L σ) (targetSymmetry A L)
    (source_normalized A Q L σ hσ) (target_normalized A L)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry
