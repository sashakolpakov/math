import OAI.RepresentationTheory.Theta.Geometric.PointBundleClasses
import OAI.RepresentationTheory.Theta.Geometric.TestDifferenceClasses

/-! # Point Difference Homomorphism -/

namespace OAI.RepresentationTheory.Theta.Geometric.PointDifferenceHomomorphism

noncomputable section

/-! The cubical identity makes the actual pointwise difference line
classes a homomorphism into the intrinsic Picard group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {d : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)

theorem groupDifferenceClass_comm (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left)
    {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (x y : T ⟶ A.scheme) :
    TestDifferenceClasses.groupDifferenceClass A.scheme a x y = TestDifferenceClasses.groupDifferenceClass A.scheme a y x := by
  unfold TestDifferenceClasses.groupDifferenceClass
  rw [mul_comm x y]
  exact mul_right_comm _ _ _

theorem pointDifferenceBundle_as_groupDifference
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) :
    PointBundleClasses.pointBundleClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) p =
      TestDifferenceClasses.groupDifferenceClass A.scheme (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
        (Over.mkIdTerminal.from A.scheme ≫ p) (𝟙 A.scheme) := by
  rw [PointBundleClasses.pointDifferenceBundle_class]
  unfold TestDifferenceClasses.groupDifferenceClass
  have hc : Picard.PicardPullback.picardPullback (Over.mkIdTerminal.from A.scheme ≫ p).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 :=
    ConstantPicardPullback.picardPullback_constant ℂ (Over.mkIdTerminal.from A.scheme).left p.left _
  rw [hc, inv_one, mul_one]
  have h : (Over.mkIdTerminal.from A.scheme ≫ p) * (𝟙 A.scheme) = DifferenceBundleTranslation.groupTranslation A.scheme p :=
    mul_comm _ _
  rw [h]
  exact congrArg (fun b => Picard.PicardPullback.picardPullback (DifferenceBundleTranslation.groupTranslation A.scheme p).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) * b⁻¹)
    (Picard.PicardPullback.picardPullback_id (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm

theorem pointDifferenceBundle_class_one (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) :
    PointBundleClasses.pointBundleClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) 1 = 1 := by
  rw [PointBundleClasses.pointDifferenceBundle_class, DifferenceBundleTranslation.groupTranslation_one]
  change Picard.PicardPullback.picardPullback (𝟙 A.scheme.left) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) * (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)⁻¹ = 1
  rw [Picard.PicardPullback.picardPullback_id, mul_inv_cancel]

theorem pointDifferenceBundle_class_mul (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hcube : ∀ (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (x y z : T ⟶ A.scheme),
      Picard.PicardPullback.picardPullback (x * y * z).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
          Picard.PicardPullback.picardPullback x.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) * Picard.PicardPullback.picardPullback y.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
          Picard.PicardPullback.picardPullback z.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
        Picard.PicardPullback.picardPullback (x * y).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
          Picard.PicardPullback.picardPullback (x * z).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
          Picard.PicardPullback.picardPullback (y * z).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
    (p q : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) :
    PointBundleClasses.pointBundleClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) (p * q) =
      PointBundleClasses.pointBundleClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) p * PointBundleClasses.pointBundleClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) q := by
  rw [pointDifferenceBundle_as_groupDifference, MonObj.comp_mul,
    groupDifferenceClass_comm A _ _ (𝟙 A.scheme), TestDifferenceClasses.groupDifferenceClass_mul_right A _ hcube,
    groupDifferenceClass_comm A _ (𝟙 A.scheme), groupDifferenceClass_comm A _ (𝟙 A.scheme)]
  rw [pointDifferenceBundle_as_groupDifference, pointDifferenceBundle_as_groupDifference]

end

end OAI.RepresentationTheory.Theta.Geometric.PointDifferenceHomomorphism
