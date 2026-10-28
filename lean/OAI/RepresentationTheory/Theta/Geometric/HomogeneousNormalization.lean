import OAI.RepresentationTheory.Theta.Geometric.MultiplicativeFamilyCriterion

/-! # Homogeneous Normalization -/

namespace OAI.RepresentationTheory.Theta.Geometric.HomogeneousNormalization

noncomputable section

/-! Normalizing a homogeneous family along the identity axis preserves
its translation invariance and its actual relative Picard class. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem homogeneous_baseTwist {T : Over S} (m : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left)
    (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) (hq : A.IsHomogeneousPicardClass T q) :
    A.IsHomogeneousPicardClass T (AlgebraicGeometry.FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.baseTwist A.scheme m q) := by
  intro U f a
  rw [AlgebraicGeometry.FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.baseTwist_natural]
  let m' := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left m
  let q' : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left := (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op q
  have ht : (A.translation a).left ≫ (fst U A.scheme).left = (fst U A.scheme).left :=
    congrArg Over.Hom.left (A.translation_fst a)
  change (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (Picard.PicardPullback.picardPullback (A.translation a).left (Picard.PicardPullback.picardPullback (fst U A.scheme).left m' * q')) =
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) (AlgebraicGeometry.FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.baseTwist A.scheme m' q')
  rw [map_mul, Picard.PicardPullback.picardPullback_comp, ht]
  exact (AlgebraicGeometry.FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.toRelativePicard_baseTwist_class A.scheme m'
      (Picard.PicardPullback.picardPullback (A.translation a).left q')).trans
    ((hq U f a).trans (AlgebraicGeometry.FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.toRelativePicard_baseTwist_class A.scheme m' q').symm)

theorem homogeneous_normalizedProductClass {T : Over S}
    (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) (hq : A.IsHomogeneousPicardClass T q) :
    A.IsHomogeneousPicardClass T (AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass A.scheme T q) := by
  have he : AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass A.scheme T q = AlgebraicGeometry.FormalGeometry.Completion.RelativePicard.Construction.RelativePicardBaseTwist.baseTwist A.scheme
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 T) (1 : T ⟶ A.scheme)).left q)⁻¹ q := by
    change q / AlgebraicGeometry.Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (fst T A.scheme).left _ =
      AlgebraicGeometry.Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (fst T A.scheme).left _ * q
    rw [map_inv, div_eq_mul_inv, mul_comm]
    rfl
  rw [he]
  exact homogeneous_baseTwist A _ q hq

end

end OAI.RepresentationTheory.Theta.Geometric.HomogeneousNormalization
