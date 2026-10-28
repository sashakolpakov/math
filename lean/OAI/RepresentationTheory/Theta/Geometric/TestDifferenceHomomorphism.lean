import OAI.RepresentationTheory.Theta.Geometric.PointDifferenceHomomorphism
import OAI.AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup

/-! # Test Difference Homomorphism -/

namespace OAI.RepresentationTheory.Theta.Geometric.TestDifferenceHomomorphism

noncomputable section

/-! The native cubical identity makes the original difference family
additive on every test scheme, including nonreduced tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {d : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hcube : ∀ (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (x y z : T ⟶ A.scheme),
      Picard.PicardPullback.picardPullback (x * y * z).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
          Picard.PicardPullback.picardPullback x.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) * Picard.PicardPullback.picardPullback y.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
          Picard.PicardPullback.picardPullback z.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
        Picard.PicardPullback.picardPullback (x * y).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
          Picard.PicardPullback.picardPullback (x * z).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
          Picard.PicardPullback.picardPullback (y * z).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))

include hcube in
theorem parameterDifferenceLineClass_mul {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (a b : T ⟶ A.scheme) :
    ParameterizedPicardClass.parameterLineClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) (a * b) =
      ParameterizedPicardClass.parameterLineClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) a *
        ParameterizedPicardClass.parameterLineClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) b := by
  rw [TestDifferenceClasses.parameterDifference_as_groupDifference, MonObj.comp_mul,
    PointDifferenceHomomorphism.groupDifferenceClass_comm A _ _ (snd T A.scheme), TestDifferenceClasses.groupDifferenceClass_mul_right A _ hcube,
    PointDifferenceHomomorphism.groupDifferenceClass_comm A _ (snd T A.scheme), PointDifferenceHomomorphism.groupDifferenceClass_comm A _ (snd T A.scheme)]
  rw [TestDifferenceClasses.parameterDifference_as_groupDifference, TestDifferenceClasses.parameterDifference_as_groupDifference]

def parameterDifferenceLineClassHom (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    (T ⟶ A.scheme) →* AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left where
  toFun := ParameterizedPicardClass.parameterLineClass (AbelianDifferenceBundle.abelianDifferenceBundle A L)
  map_one' := by
    have h := parameterDifferenceLineClass_mul A L hcube (1 : T ⟶ A.scheme) 1
    rw [one_mul] at h
    exact (mul_left_cancel ((mul_one _).trans h)).symm
  map_mul' := parameterDifferenceLineClass_mul A L hcube

def parameterDifferencePicardHom (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    (T ⟶ A.scheme) →* AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A.scheme T :=
  (AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme T).comp (parameterDifferenceLineClassHom A L hcube T)

end

end OAI.RepresentationTheory.Theta.Geometric.TestDifferenceHomomorphism
