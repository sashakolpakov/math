import OAI.RepresentationTheory.Theta.Geometric.Projective.BaseChange
import OAI.RepresentationTheory.Theta.Geometric.Affine.TestMaps

/-! # Constant Family Projective Embedding -/

namespace OAI.RepresentationTheory.Theta.Geometric.ConstantFamilyProjectiveEmbedding

noncomputable section

/-! A fixed complex projective embedding gives an actual projective
embedding after every affine parameter change. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable (A : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {n : ℕ}
    (e : A.left ⟶ Projective.Map.RelativeProjective.projectiveSpace ℂ n)
    (he : e ≫ Projective.Map.RelativeProjective.projectiveSpaceToBase ℂ n = A.hom)
    (R : Type) [CommRing R] [Algebra ℂ R]

def constantFamilyProjectiveEmbedding :
    (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⊗ A).left ⟶ Projective.Map.RelativeProjective.projectiveSpace R n :=
  (Projective.BaseChange.RelativeProjective.coefficient_isPullback (algebraMap ℂ R) n).flip.lift
    (fst (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) A).left ((snd (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) A).left ≫ e)
    (by rw [Category.assoc, he]; exact pullback.condition)

@[reassoc]
theorem constantFamilyProjectiveEmbedding_base :
    constantFamilyProjectiveEmbedding A e he R ≫ Projective.Map.RelativeProjective.projectiveSpaceToBase R n =
      (fst (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) A).left :=
  (Projective.BaseChange.RelativeProjective.coefficient_isPullback (algebraMap ℂ R) n).flip.lift_fst _ _ _

@[reassoc]
theorem constantFamilyProjectiveEmbedding_coefficient :
    constantFamilyProjectiveEmbedding A e he R ≫ Projective.Map.RelativeProjective.coefficientMap (algebraMap ℂ R) n =
      (snd (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) A).left ≫ e :=
  (Projective.BaseChange.RelativeProjective.coefficient_isPullback (algebraMap ℂ R) n).flip.lift_snd _ _ _

theorem constantFamilyProjectiveEmbedding_isPullback :
    IsPullback (constantFamilyProjectiveEmbedding A e he R)
      (snd (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) A).left
      (Projective.Map.RelativeProjective.coefficientMap (algebraMap ℂ R) n) e := by
  apply IsPullback.of_right (t :=
    (Projective.BaseChange.RelativeProjective.coefficient_isPullback (algebraMap ℂ R) n).flip) ?_
    (constantFamilyProjectiveEmbedding_coefficient A e he R)
  rw [constantFamilyProjectiveEmbedding_base, he]
  exact IsPullback.of_hasPullback (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).hom A.hom

instance constantFamilyProjectiveEmbedding_closed [IsClosedImmersion e] :
    IsClosedImmersion (constantFamilyProjectiveEmbedding A e he R) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (constantFamilyProjectiveEmbedding_isPullback A e he R).flip
    (inferInstanceAs (IsClosedImmersion e))

end

end OAI.RepresentationTheory.Theta.Geometric.ConstantFamilyProjectiveEmbedding
