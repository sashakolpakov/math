import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductPicard
import OAI.RepresentationTheory.Theta.Geometric.Picard.PicardPullback
import OAI.AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup

/-! # Rigidified Picard Difference -/

namespace OAI.RepresentationTheory.Theta.Geometric.RigidifiedPicardDifference

noncomputable section

/-! The tensor difference of two actual rigidified families represents
equality of their classes in the original relative Picard sheaf. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {K : Type u} [Field K] {A B : Over (Spec (.of K))} [GrpObj A]
    (D F : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A B)

def rigidifiedPicardDifference : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A B where
  bundle := D.bundle.tensor (AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual F.bundle)
  axis := by
    have hd : Picard.PicardPullback.picardPullback (lift (𝟙 B) (1 : B ⟶ A)).left
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle) = 1 := Quotient.sound ⟨D.axis⟩
    have hf : Picard.PicardPullback.picardPullback (lift (𝟙 B) (1 : B ⟶ A)).left
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf F.bundle) = 1 := Quotient.sound ⟨F.axis⟩
    have h : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((D.bundle.tensor (AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual F.bundle)).pullback
        (lift (𝟙 B) (1 : B ⟶ A)).left) = 1 := by
      change Picard.PicardPullback.picardPullback (lift (𝟙 B) (1 : B ⟶ A)).left
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle * (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf F.bundle)⁻¹) = 1
      rw [map_mul, map_inv, hd, hf, inv_one, mul_one]
    exact Classical.choice (Quotient.exact h)

theorem rigidifiedPicardDifference_relativeValue {T : Over (Spec (.of K))} (a : T ⟶ B) :
    (rigidifiedPicardDifference D F).relativeValue a = D.relativeValue a * (F.relativeValue a)⁻¹ := by
  change (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T)
      (Picard.PicardPullback.picardPullback (a ⊗ₘ 𝟙 A).left
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle * (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf F.bundle)⁻¹)) = _
  rw [map_mul, map_inv, AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicard_mul, AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicard_inv]
  rfl

theorem rigidifiedPicardDifference_zero_iff {T : Over (Spec (.of K))} (a : T ⟶ B) :
    (rigidifiedPicardDifference D F).relativeValue a = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T ↔
      D.relativeValue a = F.relativeValue a := by
  rw [rigidifiedPicardDifference_relativeValue, AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one,
    mul_inv_eq_one]

end

end OAI.RepresentationTheory.Theta.Geometric.RigidifiedPicardDifference
