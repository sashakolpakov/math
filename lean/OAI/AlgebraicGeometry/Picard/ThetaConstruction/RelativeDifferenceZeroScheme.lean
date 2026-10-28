import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroScheme
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceBundle

/-! # Relative Difference Zero Scheme -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric

noncomputable section

/-! The normalized difference line of the original abelian family
defines an actual zero scheme with its identity section. Its universal
property is equality in the original relative Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem relativeRigidifiedDifference_one_class (T : Over S) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).line (1 : T ⟶ A.scheme)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A.scheme).left := by
  let z := lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme)
  have he : snd T A.scheme ≫ z = (1 : T ⟶ A.scheme) ⊗ₘ 𝟙 A.scheme := by
    dsimp only [z]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst, MonObj.comp_one]
    · simp only [Category.assoc, lift_snd, tensorHom_snd, Category.comp_id]
  have hz : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback z.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)) = 1 :=
    Quotient.sound (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle_normalized_right A L)
  have hc := congrArg (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd T A.scheme).left) hz
  rw [RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp, map_one] at hc
  have hl : (snd T A.scheme).left ≫ z.left = ((1 : T ⟶ A.scheme) ⊗ₘ 𝟙 A.scheme).left :=
    congrArg Over.Hom.left he
  exact (congrArg (fun f => RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)))
    hl).symm.trans hc

theorem relativeRigidifiedDifference_one (T : Over S) :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue (1 : T ⟶ A.scheme) =
      AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A.scheme T := by
  exact congrArg (fun c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left =>
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) c) (relativeRigidifiedDifference_one_class A L T)

variable [IsLocallyNoetherian S] (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme)

local instance : IsLocallyNoetherian A.scheme.left := LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom

def relativeDifferenceZeroFamily : Over S :=
  RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroSchemeOver (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) P

def relativeDifferenceZeroInclusion : relativeDifferenceZeroFamily A L P ⟶ A.scheme :=
  RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) P

theorem relativeDifferenceZero_factorization (T : Over S) (a : T ⟶ A.scheme) :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A.scheme T ↔
      ∃ z : T ⟶ relativeDifferenceZeroFamily A L P, z ≫ relativeDifferenceZeroInclusion A L P = a :=
  RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion_factorization (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) P T a

theorem relativeDifferenceZero_identity_section :
    ∃ e : Over.mk (𝟙 S) ⟶ relativeDifferenceZeroFamily A L P,
      e ≫ relativeDifferenceZeroInclusion A L P = (1 : Over.mk (𝟙 S) ⟶ A.scheme) :=
  (relativeDifferenceZero_factorization A L P (Over.mk (𝟙 S)) 1).mp
    (relativeRigidifiedDifference_one A L (Over.mk (𝟙 S)))

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric
