import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.OriginRatios
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.SubgroupFiberCommutativity
import OAI.AlgebraicGeometry.Picard.PoincareBundle.EqualOriginRatiosCommutation

/-! # Translation Commutation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.TranslationCommutation

noncomputable section

/-! Isotropy makes the two actual subgroup translations from the origin commute. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios

variable {k : Type u} [Field k] {H A : Over (Spec (.of k))} [GrpObj H] [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] (i : H ⟶ A) [IsMonHom i]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)
  (u : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule H.left ≅ Line.Fibers.fiber L i)
  (o : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅ Line.Fibers.fiber L η[A])
  (he : (Scheme.Modules.pullback (β_ A A).hom.left).mapIso (InducingFormulaSymmetry.regrouped A Q L e) ≪≫ InducingFormulaSymmetry.targetSymmetry A L =
    InducingFormulaSymmetry.sourceSymmetry A Q L σ ≪≫ InducingFormulaSymmetry.regrouped A Q L e)
  (hi : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ H), Kernel.IntersectionFrames.obstruction i i (Line.Comparison.Bundle.fromShared Q) s
    (Symmetric.KernelTrivialization.secondFrame i (Line.Comparison.Bundle.fromShared Q) s σ) a b = 1)

include he hi o

/-- The two actual line-isomorphism paths from the origin agree on every test scheme. -/
theorem paths_commute {T : Over (Spec (.of k))} (a b : T ⟶ H) (z : T ⟶ A)
    (hab : (a ≫ i) * (b ≫ i) = z) (hba : (b ≫ i) * (a ≫ i) = z) :
    Subgroup.TranslationFibers.transportIso i L (FramedSubgroupInducingProduct.translationIso i Q L e s u)
        (1 : T ⟶ A) (a ≫ i) a (mul_one (a ≫ i)) ≪≫
      Subgroup.TranslationFibers.transportIso i L (FramedSubgroupInducingProduct.translationIso i Q L e s u) (a ≫ i) z b hba =
    Subgroup.TranslationFibers.transportIso i L (FramedSubgroupInducingProduct.translationIso i Q L e s u)
        (1 : T ⟶ A) (b ≫ i) b (mul_one (b ≫ i)) ≪≫
      Subgroup.TranslationFibers.transportIso i L (FramedSubgroupInducingProduct.translationIso i Q L e s u) (b ≫ i) z a hab :=
  EqualOriginRatiosCommutation.paths_commute (FiberIsomorphismRatios.fiberLine L (1 : T ⟶ A))
    (FramedSubgroupFiberProducts.atPoint i Q L e s a (b ≫ i) z hab)
    (FramedSubgroupFiberProducts.atPoint i Q L e s b (a ≫ i) z hba)
    (SubgroupFiberCommutativity.commutative i Q L s σ e he hi a b z hab hba)
    (Subgroup.TranslationFibers.transportIso i L (FramedSubgroupInducingProduct.translationIso i Q L e s u)
      (1 : T ⟶ A) (a ≫ i) a (mul_one (a ≫ i)))
    (Subgroup.TranslationFibers.transportIso i L (FramedSubgroupInducingProduct.translationIso i Q L e s u)
      (1 : T ⟶ A) (b ≫ i) b (mul_one (b ≫ i)))
    (Subgroup.TranslationFibers.transportIso i L (FramedSubgroupInducingProduct.translationIso i Q L e s u) (a ≫ i) z b hba)
    (Subgroup.TranslationFibers.transportIso i L (FramedSubgroupInducingProduct.translationIso i Q L e s u) (b ≫ i) z a hab)
    (NaturalOriginLineFrames.frame L o T).symm
    (GlobalPullbackFrame.atPoint i L u a (a ≫ i) rfl) (GlobalPullbackFrame.atPoint i L u b (b ≫ i) rfl)
    (OriginRatios.originRatio_uniform i Q L e s
      (Symmetric.KernelTrivialization.secondFrame i (Line.Comparison.Bundle.fromShared Q) s σ) u o hi a b)
    (FramedSubgroupFiberProducts.transport_contraction i Q L e s u b (a ≫ i) z hba)
    (FramedSubgroupFiberProducts.transport_contraction i Q L e s u a (b ≫ i) z hab)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.TranslationCommutation
