import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReducedLocalCube
import OAI.RepresentationTheory.Theta.Geometric.TestDifferenceClasses
import OAI.RepresentationTheory.Theta.Geometric.Picard.BaseTwists

/-! # Reduced Local Difference Homogeneity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReducedLocalDifferenceHomogeneity.Geometric

noncomputable section

/-! The proved original-base cube identity gives homogeneity of the
actual normalized difference bundle on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem relativeDifference_parameter_class {U : Over S} (a : U ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) a =
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
        (fst U A.scheme ≫ a) (snd U A.scheme) := by
  let M := RelativeDifferenceBundle.Geometric.identityNormalizedLine A L
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
    [IsLocallyNoetherian S] [IsReduced S] (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme)

include P in
theorem reducedLocal_groupDifference_mul_right {U : Over S} (a b c : U ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a (b * c) =
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a b *
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a c := by
  have hc := div_eq_one.mp (ReducedLocalCube.Geometric.reducedLocal_cube A P L a b c)
  have h := RepresentationTheory.Theta.Geometric.Cubical.ClassPullback.cubical_group_difference _ _ _ _ _ _ _ hc
  simpa only [RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass, mul_assoc] using h

include P in
theorem reducedLocal_difference_translate_class {U : Over S} (a b : U ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation b).left (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) a) =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) a *
        RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (fst U A.scheme).left
          (RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a b) := by
  rw [relativeDifference_parameter_class, RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass_pullback]
  simp only [← Category.assoc, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation_fst, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation_snd]
  rw [reducedLocal_groupDifference_mul_right A L P]
  exact (mul_comm _ _).trans (congrArg₂ (fun x y => x * y) rfl
    (RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass_pullback A.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
      (fst U A.scheme) a b).symm)

include P in
theorem reducedLocal_difference_homogeneous :
    A.IsHomogeneousPicardClass A.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)) := by
  intro U f a
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) f)) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) f)
  rw [reducedLocal_difference_translate_class A L P]
  exact RepresentationTheory.Theta.Geometric.Picard.BaseTwists.relativePicard_tensor_base A.scheme U _ _

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReducedLocalDifferenceHomogeneity.Geometric
