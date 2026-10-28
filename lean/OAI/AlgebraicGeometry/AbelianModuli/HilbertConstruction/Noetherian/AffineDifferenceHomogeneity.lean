import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineRelativeCube
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.DifferenceHomogeneity

/-! # Affine Difference Homogeneity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineDifferenceHomogeneity.Theta.Geometric

noncomputable section

/-! The original normalized difference line is homogeneous over every
Noetherian affine base. The Picard equality ranges over all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
    {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)

include P

theorem noetherianAffine_groupDifference_mul_right {U : Over S} (a b c : U ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a (b * c) =
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a b *
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a c := by
  have hc := div_eq_one.mp (AffineRelativeCube.Theta.Geometric.noetherianAffine_cube A P L a b c)
  have h := RepresentationTheory.Theta.Geometric.Cubical.ClassPullback.cubical_group_difference _ _ _ _ _ _ _ hc
  simpa only [RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass, mul_assoc] using h

theorem noetherianAffine_difference_translate_class {U : Over S} (a b : U ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation b).left (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) a) =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) a *
        RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (fst U A.scheme).left
          (RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a b) := by
  rw [Local.DifferenceHomogeneity.Theta.Geometric.local_difference_parameter_class, RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass_pullback]
  simp only [← Category.assoc, Abelian.Schemes.AbelianScheme.translation_fst, Abelian.Schemes.AbelianScheme.translation_snd]
  rw [noetherianAffine_groupDifference_mul_right A L P]
  exact (mul_comm _ _).trans (congrArg₂ (fun x y => x * y) rfl
    (RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass_pullback A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
      (fst U A.scheme) a b).symm)

theorem noetherianAffine_difference_homogeneous :
    A.IsHomogeneousPicardClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)) := by
  intro U f a
  change (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) f)) =
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) f)
  rw [noetherianAffine_difference_translate_class A L P]
  exact RepresentationTheory.Theta.Geometric.Picard.BaseTwists.relativePicard_tensor_base A.scheme U _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineDifferenceHomogeneity.Theta.Geometric
