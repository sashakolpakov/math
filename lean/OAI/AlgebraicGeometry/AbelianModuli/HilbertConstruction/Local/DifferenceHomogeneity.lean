import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.RelativeCube
import OAI.RepresentationTheory.Theta.Geometric.TestDifferenceClasses
import OAI.RepresentationTheory.Theta.Geometric.Picard.BaseTwists

/-! # Difference Homogeneity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.DifferenceHomogeneity.Theta.Geometric

noncomputable section

/-! The genuine local cube identity makes the original normalized
relative difference bundle homogeneous on all test schemes, including
nonreduced tests and nonreduced Noetherian local bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)

theorem local_difference_parameter_class {U : Over S} (a : U ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) a =
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
        (fst U A.scheme ≫ a) (snd U A.scheme) := by
  let M := Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L
  have hm : (a ⊗ₘ 𝟙 A.scheme) ≫ μ[A.scheme] = (fst U A.scheme ≫ a) * snd U A.scheme := by
    have he : μ[A.scheme] = fst A.scheme A.scheme * snd A.scheme A.scheme := by
      change μ[A.scheme] = lift (fst A.scheme A.scheme) (snd A.scheme A.scheme) ≫ μ[A.scheme]
      simp only [lift_fst_snd, Category.id_comp]
    rw [he, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, Category.comp_id]
  have h := RepresentationTheory.Theta.Geometric.Picard.PicardPullback.algebraicDifferenceBundle_pullback_class M (fst A.scheme A.scheme).left
    (snd A.scheme A.scheme).left μ[A.scheme].left (a ⊗ₘ 𝟙 A.scheme).left
  rw [show (a ⊗ₘ 𝟙 A.scheme).left ≫ μ[A.scheme].left =
      ((fst U A.scheme ≫ a) * snd U A.scheme).left from congrArg Over.Hom.left hm,
    show (a ⊗ₘ 𝟙 A.scheme).left ≫ (fst A.scheme A.scheme).left =
      (fst U A.scheme ≫ a).left from congrArg Over.Hom.left (tensorHom_fst a (𝟙 A.scheme)),
    show (a ⊗ₘ 𝟙 A.scheme).left ≫ (snd A.scheme A.scheme).left =
      (snd U A.scheme).left from congrArg Over.Hom.left
        ((tensorHom_snd a (𝟙 A.scheme)).trans (Category.comp_id _))] at h
  exact h

variable [IsAffine S] [IsLocalRing Γ(S, ⊤)] [IsNoetherianRing Γ(S, ⊤)]
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)

include P in
theorem local_groupDifference_mul_right {U : Over S} (a b c : U ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a (b * c) =
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a b *
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a c := by
  have hc := div_eq_one.mp (RelativeCube.Theta.Geometric.local_cube A P L a b c)
  have h := RepresentationTheory.Theta.Geometric.Cubical.ClassPullback.cubical_group_difference _ _ _ _ _ _ _ hc
  simpa only [RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass, mul_assoc] using h

include P in
theorem local_difference_translate_class {U : Over S} (a b : U ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation b).left (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) a) =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) a *
        RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (fst U A.scheme).left
          (RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a b) := by
  rw [local_difference_parameter_class, RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass_pullback]
  simp only [← Category.assoc, Abelian.Schemes.AbelianScheme.translation_fst, Abelian.Schemes.AbelianScheme.translation_snd]
  rw [local_groupDifference_mul_right A L P]
  exact (mul_comm _ _).trans (congrArg₂ (fun x y => x * y) rfl
    (RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass_pullback A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
      (fst U A.scheme) a b).symm)

include P in
theorem local_difference_homogeneous :
    A.IsHomogeneousPicardClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)) := by
  intro U f a
  change (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) f)) =
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) f)
  rw [local_difference_translate_class A L P]
  exact RepresentationTheory.Theta.Geometric.Picard.BaseTwists.relativePicard_tensor_base A.scheme U _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.DifferenceHomogeneity.Theta.Geometric
