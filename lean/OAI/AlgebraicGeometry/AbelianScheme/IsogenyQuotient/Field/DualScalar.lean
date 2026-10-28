import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarLine
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPoincare

/-! # Dual Scalar -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.DualScalar.Construction

noncomputable section

/-! The actual Poincare scalar comparison proves that the original
native dual of multiplication by n is multiplication by n. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

set_option backward.isDefEq.respectTransparency false in
theorem field_nativeDualMap_scalar
    {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (n : ℕ) :
    FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap ((𝟙 A.scheme) ^ n) D D = (𝟙 D.abelian.scheme) ^ n := by
  apply Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_injective D D.abelian.scheme
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op D.abelian.scheme)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap ((𝟙 A.scheme) ^ n) D D ⊗ₘ 𝟙 A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op D.abelian.scheme)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((𝟙 D.abelian.scheme) ^ n ⊗ₘ 𝟙 A.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
  rw [FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback.dualMap_poincare]
  apply congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op D.abelian.scheme))
  have hl : ((𝟙 D.abelian.scheme) ^ n ⊗ₘ 𝟙 A.scheme) =
      lift ((fst D.abelian.scheme A.scheme) ^ n) (snd D.abelian.scheme A.scheme) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_pow]
  have hr : (𝟙 D.abelian.scheme ⊗ₘ (𝟙 A.scheme) ^ n) =
      lift (fst D.abelian.scheme A.scheme) ((snd D.abelian.scheme A.scheme) ^ n) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_pow]
  rw [hl, hr]
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Poincare.ProductIsomorphisms.Construction.poincarePointLine D ((fst D.abelian.scheme A.scheme) ^ n)
      (snd D.abelian.scheme A.scheme)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Poincare.ProductIsomorphisms.Construction.poincarePointLine D (fst D.abelian.scheme A.scheme)
        ((snd D.abelian.scheme A.scheme) ^ n)) :=
    Quotient.sound ⟨Poincare.ScalarLine.Construction.poincareGlobalScalarComparison D n⟩
  exact hc.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.DualScalar.Construction
