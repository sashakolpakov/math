import OAI.AlgebraicGeometry.Picard.PoincareBundle.RestrictedBilinearEquivariance
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrameExchange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaFieldSymmetry

/-! # Inducing Product Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.InducingProductSymmetry

noncomputable section

/-! Isotropy gives symmetry of the actual inducing-line product on the full subgroup intersection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

variable {S : Scheme.{u}} {H A : Over S} [GrpObj A] [IsCommMonObj A] (i : H ⟶ A)
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])

/-- The actual product after inserting the canonical intersection frame in the Poincare factor. -/
def product :
    (Scheme.Modules.pullback (i ⊗ₘ i).left).obj (InducingFormulaSymmetry.factorLine A L).sheaf ⟶
      (Scheme.Modules.pullback (i ⊗ₘ i).left).obj (InducingFormulaSymmetry.targetLine A L).sheaf :=
  Bilinear.Contraction.contractLeft (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _
    (RestrictedBilinearEquivariance.formula (i ⊗ₘ i) (Line.Comparison.Bundle.fromShared Q)
      (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L)) (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.targetLine A L)) (InducingFormulaSymmetry.regrouped A Q L e)).hom)
    (Kernel.IntersectionFrames.horizontalFrame i i (Line.Comparison.Bundle.fromShared Q) s).hom

instance product_isIso : IsIso (product i Q L s e) := by
  let β := AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _
    (RestrictedBilinearEquivariance.formula (i ⊗ₘ i) (Line.Comparison.Bundle.fromShared Q)
      (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L)) (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.targetLine A L)) (InducingFormulaSymmetry.regrouped A Q L e)).hom
  have : IsIso (Bilinear.BilinearPullback.toHom β) := by
    dsimp only [β, Bilinear.BilinearPullback.toHom]
    rw [Equiv.symm_apply_apply]
    infer_instance
  have hs : IsIso (Kernel.IntersectionFrames.horizontalFrame i i (Line.Comparison.Bundle.fromShared Q) s).hom := by infer_instance
  exact @Bilinear.Contraction.contractLeft_isIso _ _ _ _ β (Kernel.IntersectionFrames.horizontalFrame i i (Line.Comparison.Bundle.fromShared Q) s).hom hs inferInstance

/-- The natural product is symmetric whenever the actual formula intertwines the original symmetry
and the scheme-valued kernel obstruction is trivial. -/
theorem equivariant
    (he : (Scheme.Modules.pullback (β_ A A).hom.left).mapIso (InducingFormulaSymmetry.regrouped A Q L e) ≪≫ InducingFormulaSymmetry.targetSymmetry A L =
      InducingFormulaSymmetry.sourceSymmetry A Q L σ ≪≫ InducingFormulaSymmetry.regrouped A Q L e)
    (hi : ∀ (T : Over S) (a b : T ⟶ H),
      Kernel.IntersectionFrames.obstruction i i (Line.Comparison.Bundle.fromShared Q) s (Symmetric.KernelTrivialization.secondFrame i (Line.Comparison.Bundle.fromShared Q) s σ) a b = 1) :
    (Scheme.Modules.pullback (β_ H H).hom.left).map (product i Q L s e) ≫
        (RestrictedLineEquivariance.symmetry (i ⊗ₘ i) (β_ A A).hom (β_ H H).hom
          (Kernel.IntersectionSymmetry.swap_square i) (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.targetLine A L)) (InducingFormulaSymmetry.targetSymmetry A L)).hom =
      (RestrictedLineEquivariance.symmetry (i ⊗ₘ i) (β_ A A).hom (β_ H H).hom
          (Kernel.IntersectionSymmetry.swap_square i) (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L))
          (ExternalTensorSymmetry.symmetry A L)).hom ≫ product i Q L s e :=
  RestrictedBilinearEquivariance.contraction_equivariant (i ⊗ₘ i) (β_ A A).hom (β_ H H).hom
    (Kernel.IntersectionSymmetry.swap_square i) (Line.Comparison.Bundle.fromShared Q) (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L))
    (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.targetLine A L)) σ (ExternalTensorSymmetry.symmetry A L) (InducingFormulaSymmetry.targetSymmetry A L)
    (InducingFormulaSymmetry.regrouped A Q L e) he (Kernel.IntersectionFrames.horizontalFrame i i (Line.Comparison.Bundle.fromShared Q) s).hom
    (Kernel.IntersectionFrameExchange.isotropic_section i (Line.Comparison.Bundle.fromShared Q) s σ hi)

/-- The formula symmetry is derived from its diagonal normalization before isotropic contraction. -/
theorem equivariant_of_diagonal [IsIso (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left.appTop]
    (hσ : (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso σ =
      AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison A Q)
    (hi : ∀ (T : Over S) (a b : T ⟶ H),
      Kernel.IntersectionFrames.obstruction i i (Line.Comparison.Bundle.fromShared Q) s (Symmetric.KernelTrivialization.secondFrame i (Line.Comparison.Bundle.fromShared Q) s σ) a b = 1) :
    (Scheme.Modules.pullback (β_ H H).hom.left).map (product i Q L s e) ≫
        (RestrictedLineEquivariance.symmetry (i ⊗ₘ i) (β_ A A).hom (β_ H H).hom
          (Kernel.IntersectionSymmetry.swap_square i) (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.targetLine A L)) (InducingFormulaSymmetry.targetSymmetry A L)).hom =
      (RestrictedLineEquivariance.symmetry (i ⊗ₘ i) (β_ A A).hom (β_ H H).hom
          (Kernel.IntersectionSymmetry.swap_square i) (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L))
          (ExternalTensorSymmetry.symmetry A L)).hom ≫ product i Q L s e :=
  equivariant i Q L s σ e (InducingFormulaSymmetry.formula_equivariant A Q L σ e hσ) hi

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.InducingProductSymmetry
