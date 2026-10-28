import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.PresentedInducingProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.FramePointSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.InducingProductPresentation

/-! # Subgroup Fiber Commutativity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.SubgroupFiberCommutativity

noncomputable section

/-! Isotropy forces the actual subgroup inducing product to commute on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames

theorem sections_of_swap {X : Scheme.{u}} {M N P : X.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (other : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap N M P)
    (h : Bilinear.BilinearPullback.toHom other = (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso N M).hom ≫ Bilinear.BilinearPullback.toHom β)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) : β.app U m n = other.app U n m := by
  have hc := congrArg (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv N M P) h
  have hf : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv N M P ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso N M).hom ≫ Bilinear.BilinearPullback.toHom β) =
      AbelianScheme.IsogenyQuotient.BilinearFlip.Construction.flipLineBilinear β := by
    rw [AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, AbelianScheme.IsogenyQuotient.TensorSymmetrySections.Construction.tensorModuleCommIso_bilinear,
      ← AbelianScheme.IsogenyQuotient.BilinearFlip.Construction.flipLineBilinear_postcomp, ← Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear_postcomp]
    exact congrArg AbelianScheme.IsogenyQuotient.BilinearFlip.Construction.flipLineBilinear ((AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P).apply_symm_apply β)
  have he : other = AbelianScheme.IsogenyQuotient.BilinearFlip.Construction.flipLineBilinear β :=
    ((AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv N M P).apply_symm_apply other).symm.trans (hc.trans hf)
  exact (congrArg (fun f => f.app U n m) he).symm

variable {S : Scheme.{u}} {H A : Over S} [GrpObj A] [IsCommMonObj A] (i : H ⟶ A)
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (he : (Scheme.Modules.pullback (β_ A A).hom.left).mapIso (InducingFormulaSymmetry.regrouped A Q L e) ≪≫ InducingFormulaSymmetry.targetSymmetry A L =
    InducingFormulaSymmetry.sourceSymmetry A Q L σ ≪≫ InducingFormulaSymmetry.regrouped A Q L e)
  (hi : ∀ (T : Over S) (a b : T ⟶ H), Kernel.IntersectionFrames.obstruction i i (Line.Comparison.Bundle.fromShared Q) s
    (Symmetric.KernelTrivialization.secondFrame i (Line.Comparison.Bundle.fromShared Q) s σ) a b = 1)

include he hi

/-- The full actual fiber product has exactly the canonical tensor-exchange equation. -/
theorem tensor_commutation {T : Over S} (a b : T ⟶ H) (z : T ⟶ A)
    (hab : (a ≫ i) * (b ≫ i) = z) (hba : (b ≫ i) * (a ≫ i) = z) :
    Bilinear.BilinearPullback.toHom (FramedSubgroupFiberProducts.atPoint i Q L e s b (a ≫ i) z hba) =
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso (Line.Fibers.fiber L (b ≫ i)) (Line.Fibers.fiber L (a ≫ i))).hom ≫
        Bilinear.BilinearPullback.toHom (FramedSubgroupFiberProducts.atPoint i Q L e s a (b ≫ i) z hab) := by
  let q := lift (a ≫ i) (b ≫ i)
  have hx : (q ≫ (β_ A A).hom) ≫ fst A A = b ≫ i := by
    rw [Category.assoc, braiding_hom_fst, lift_snd]
  have hy : (q ≫ (β_ A A).hom) ≫ snd A A = a ≫ i := by
    rw [Category.assoc, braiding_hom_snd, lift_fst]
  have hz : (q ≫ (β_ A A).hom) ≫ μ[A] = z := by
    rw [Category.assoc, IsCommMonObj.mul_comm]
    exact hab
  have hp := Symmetric.PresentedInducingProduct.exchanged Q L σ e he q (a ≫ i) (b ≫ i) z
    (lift_fst _ _) (lift_snd _ _) hab hx hy hz
    (GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 A) (Line.Comparison.Bundle.fromShared Q) s (lift b (a ≫ i))
      (q ≫ (β_ A A).hom) (FramePointSymmetry.exchanged_pair i a b))
    (GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 A) (Line.Comparison.Bundle.fromShared Q) s (lift a (b ≫ i)) q
      (IntersectionFrameValues.horizontal_pair i i a b))
    (FramePointSymmetry.frame_symmetry i (Line.Comparison.Bundle.fromShared Q) s σ hi a b)
  have hb := Subgroup.InducingProductPresentation.atPoint_toHom_at i Q L e s b (a ≫ i) z hba
    (q ≫ (β_ A A).hom) (FramePointSymmetry.exchanged_pair i a b) hx hy hz
  have ha := Subgroup.InducingProductPresentation.atPoint_toHom_at i Q L e s a (b ≫ i) z hab
    q (IntersectionFrameValues.horizontal_pair i i a b) (lift_fst _ _) (lift_snd _ _) hab
  exact hb.trans ((congrArg Iso.hom hp).trans
    (congrArg (fun f => (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso (Line.Fibers.fiber L (b ≫ i)) (Line.Fibers.fiber L (a ≫ i))).hom ≫ f) ha.symm))

/-- Commutativity holds on sections of every open of every test scheme, including infinitesimal schemes. -/
theorem commutative {T : Over S} (a b : T ⟶ H) (z : T ⟶ A)
    (hab : (a ≫ i) * (b ≫ i) = z) (hba : (b ≫ i) * (a ≫ i) = z)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L (a ≫ i), U)) (n : Γ(Line.Fibers.fiber L (b ≫ i), U)) :
    (FramedSubgroupFiberProducts.atPoint i Q L e s a (b ≫ i) z hab).app U m n =
      (FramedSubgroupFiberProducts.atPoint i Q L e s b (a ≫ i) z hba).app U n m :=
  sections_of_swap _ _ (tensor_commutation i Q L s σ e he hi a b z hab hba) U m n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.SubgroupFiberCommutativity
