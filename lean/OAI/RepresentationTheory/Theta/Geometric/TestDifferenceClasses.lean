import OAI.RepresentationTheory.Theta.Geometric.DifferencePicardClasses
import OAI.RepresentationTheory.Theta.Geometric.Cubical.ClassPullback

/-! # Test Difference Classes -/

namespace OAI.RepresentationTheory.Theta.Geometric.TestDifferenceClasses

noncomputable section

/-! Difference classes and their pullbacks, with the actual group law
and line bundle on an arbitrary abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

def groupDifferenceClass {S : Scheme} (A : Over S) [GrpObj A]
    (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.left) {T : Over S} (x y : T ⟶ A) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left :=
  Picard.PicardPullback.picardPullback (x * y).left a * (Picard.PicardPullback.picardPullback x.left a)⁻¹ * (Picard.PicardPullback.picardPullback y.left a)⁻¹

theorem groupDifferenceClass_pullback {S : Scheme} (A : Over S) [GrpObj A]
    (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.left) {T U : Over S} (f : U ⟶ T) (x y : T ⟶ A) :
    Picard.PicardPullback.picardPullback f.left (groupDifferenceClass A a x y) =
      groupDifferenceClass A a (f ≫ x) (f ≫ y) := by
  simp only [groupDifferenceClass, map_mul, map_inv, Picard.PicardPullback.picardPullback_comp]
  congr 2
  exact congrArg (fun h => Picard.PicardPullback.picardPullback h a) (congrArg Over.Hom.left (MonObj.comp_mul f x y))

theorem parameterDifference_as_groupDifference {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (t : T ⟶ A.scheme) :
    ParameterizedPicardClass.parameterLineClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) t =
      groupDifferenceClass A.scheme (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) (fst T A.scheme ≫ t) (snd T A.scheme) := by
  rw [DifferencePicardClasses.parameterDifference_class, Picard.PicardPullback.picardPullback_comp, Picard.PicardPullback.picardPullback_comp]
  change Picard.PicardPullback.picardPullback (A.translation t ≫ snd T A.scheme).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
    (Picard.PicardPullback.picardPullback (fst T A.scheme ≫ t).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))⁻¹ *
    (Picard.PicardPullback.picardPullback (snd T A.scheme).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))⁻¹ = _
  rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation_snd]
  rfl

theorem groupDifferenceClass_mul_right {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left)
    (hcube : ∀ (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (x y z : T ⟶ A.scheme),
      Picard.PicardPullback.picardPullback (x * y * z).left a * Picard.PicardPullback.picardPullback x.left a * Picard.PicardPullback.picardPullback y.left a *
        Picard.PicardPullback.picardPullback z.left a = Picard.PicardPullback.picardPullback (x * y).left a *
          Picard.PicardPullback.picardPullback (x * z).left a * Picard.PicardPullback.picardPullback (y * z).left a)
    {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (x y z : T ⟶ A.scheme) :
    groupDifferenceClass A.scheme a x (y * z) =
      groupDifferenceClass A.scheme a x y * groupDifferenceClass A.scheme a x z := by
  have H := Cubical.ClassPullback.cubical_group_difference _ _ _ _ _ _ _ (hcube T x y z)
  simpa only [groupDifferenceClass, mul_assoc] using H

end

end OAI.RepresentationTheory.Theta.Geometric.TestDifferenceClasses
