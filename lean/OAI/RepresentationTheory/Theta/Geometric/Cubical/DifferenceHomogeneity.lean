import OAI.RepresentationTheory.Theta.Geometric.TestDifferenceClasses
import OAI.RepresentationTheory.Theta.Geometric.Picard.BaseTwists

/-! # Difference Homogeneity -/

namespace OAI.RepresentationTheory.Theta.Geometric.Cubical.DifferenceHomogeneity

noncomputable section

/-! The cubical identity proves homogeneity of the actual difference
bundle in the fppf relative Picard sheaf, on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hcube : ∀ (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (x y z : T ⟶ A.scheme),
      Picard.PicardPullback.picardPullback (x * y * z).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
        Picard.PicardPullback.picardPullback x.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) * Picard.PicardPullback.picardPullback y.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
        Picard.PicardPullback.picardPullback z.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      Picard.PicardPullback.picardPullback (x * y).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
        Picard.PicardPullback.picardPullback (x * z).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
        Picard.PicardPullback.picardPullback (y * z).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))

include hcube

theorem parameterDifference_translate_class {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (t u : T ⟶ A.scheme) :
    Picard.PicardPullback.picardPullback (A.translation u).left (ParameterizedPicardClass.parameterLineClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) t) =
      ParameterizedPicardClass.parameterLineClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) t *
        Picard.PicardPullback.picardPullback (fst T A.scheme).left (TestDifferenceClasses.groupDifferenceClass A.scheme (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) t u) := by
  rw [TestDifferenceClasses.parameterDifference_as_groupDifference, TestDifferenceClasses.groupDifferenceClass_pullback]
  simp only [← Category.assoc, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation_fst, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation_snd]
  rw [TestDifferenceClasses.groupDifferenceClass_mul_right A _ hcube]
  exact (mul_comm _ _).trans (congrArg₂ (fun x y => x * y)
    rfl
    (TestDifferenceClasses.groupDifferenceClass_pullback A.scheme (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) (fst T A.scheme) t u).symm)

theorem abelianDifferenceBundle_homogeneous :
    A.IsHomogeneousPicardClass A.scheme (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianDifferenceBundle.abelianDifferenceBundle A L)) := by
  intro U f a
  change (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (Picard.PicardPullback.picardPullback (A.translation a).left (ParameterizedPicardClass.parameterLineClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) f)) =
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) (ParameterizedPicardClass.parameterLineClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) f)
  rw [parameterDifference_translate_class A L hcube]
  exact Picard.BaseTwists.relativePicard_tensor_base A.scheme U _ _

end

end OAI.RepresentationTheory.Theta.Geometric.Cubical.DifferenceHomogeneity
