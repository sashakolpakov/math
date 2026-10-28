import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BundleIsoOpenDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineDifferenceHomogeneity

/-! # Relative Cube -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.RelativeCube.Theta.Geometric

noncomputable section

/-! The normalized cube identity and homogeneous difference line over
an arbitrary locally Noetherian base, obtained from the actual affine
cube identities by normalized line-isomorphism descent. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BundleIsoOpenDescent

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (L : Line.Bundles.LineBundle A.scheme.left)

include P

theorem locallyNoetherian_universal_cube :
    Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
      (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A) = 1 := by
  let PC : Projective.ProjectivePresentations.ProjectivePresentation (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A) := (P.product P).product P
  let q := Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
    (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A)
  let C : Line.Bundles.LineBundle (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).left := q.out
  have hC : Line.Bundles.LineBundle.classOf C = q := Quotient.out_eq _
  let z : Over.mk (𝟙 S) ⟶ Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A := 1
  have hz : z.left ≫ (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom = 𝟙 S := z.w
  have hr : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback z.left (Line.Bundles.LineBundle.classOf C) = 1 := by
    rw [hC]
    change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback z.left
      (Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
        (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A)) = 1
    rw [Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass_pullback]
    simp only [z, MonObj.one_comp, Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass,
      Picard.ThetaConstruction.RelativeCubeClasses.Geometric.identityNormalizedLine_one_class, mul_one, div_one]
  let zero : (C.pullback z.left).sheaf ≅ Line.Bundles.structureModule S :=
    Classical.choice (Quotient.exact hr)
  let b : (C.pullback z.left).sheaf ≅
      ((Line.Bundles.LineBundle.trivial (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).left).pullback z.left).sheaf :=
    zero ≪≫ (Line.Bundles.structureModulePullbackIso z.left).symm
  obtain ⟨e⟩ := Projective.BundleIsoOpenDescent.projective_bundleIso_of_openCover PC z.left hz C
    (Line.Bundles.LineBundle.trivial (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).left) b S.affineCover (by
      intro i
      let f := S.affineCover.f i
      have hc : Line.Bundles.LineBundle.pullbackClass (pullback.fst (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom f)
          (Line.Bundles.LineBundle.classOf C) = 1 := by
        rw [hC]
        change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom f)
          (Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
            (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A)) = 1
        rw [Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass_baseChange, IdentityNormalizationBaseChange.Theta.Geometric.identityNormalizedLine_baseChange_class]
        exact Noetherian.AffineRelativeCube.Theta.Geometric.noetherianAffine_cube (A.pullback f) (P.baseChange f)
          (L.pullback (pullback.fst A.scheme.hom f)) _ _ _
      let frame : (C.pullback (pullback.fst (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom f)).sheaf ≅
          Line.Bundles.structureModule (pullback (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom f) :=
        Classical.choice (Quotient.exact hc)
      exact ⟨frame ≪≫ (Line.Bundles.structureModulePullbackIso
        (pullback.fst (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom f)).symm⟩)
  exact hC.symm.trans (Quotient.sound ⟨e⟩)

theorem locallyNoetherian_cube {T : Over S} (a b c : T ⟶ A.scheme) :
    Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a b c = 1 :=
  Relative.CubeProducts.Theta.Geometric.relativeCubeClass_eq_of_universal A _ (locallyNoetherian_universal_cube A P L) a b c

theorem locallyNoetherian_groupDifference_mul_right {T : Over S} (a b c : T ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a (b * c) =
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a b *
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a c := by
  have hc := div_eq_one.mp (locallyNoetherian_cube A P L a b c)
  have h := RepresentationTheory.Theta.Geometric.Cubical.ClassPullback.cubical_group_difference _ _ _ _ _ _ _ hc
  simpa only [RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass, mul_assoc] using h

theorem locallyNoetherian_difference_translate_class {T : Over S} (a b : T ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation b).left (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) a) =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) a *
        RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (fst T A.scheme).left
          (RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a b) := by
  rw [Local.DifferenceHomogeneity.Theta.Geometric.local_difference_parameter_class, RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass_pullback]
  simp only [← Category.assoc, Abelian.Schemes.AbelianScheme.translation_fst, Abelian.Schemes.AbelianScheme.translation_snd]
  rw [locallyNoetherian_groupDifference_mul_right A P L]
  exact (mul_comm _ _).trans (congrArg₂ (fun x y => x * y) rfl
    (RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass_pullback A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
      (fst T A.scheme) a b).symm)

theorem locallyNoetherian_difference_homogeneous :
    A.IsHomogeneousPicardClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)) := by
  intro T f a
  change (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) f)) =
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) f)
  rw [locallyNoetherian_difference_translate_class A P L]
  exact RepresentationTheory.Theta.Geometric.Picard.BaseTwists.relativePicard_tensor_base A.scheme T _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.RelativeCube.Theta.Geometric
