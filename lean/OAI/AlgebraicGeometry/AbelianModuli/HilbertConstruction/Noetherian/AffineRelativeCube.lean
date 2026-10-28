import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.RelativeCube
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.StalkFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdentityNormalizationBaseChange

/-! # Affine Relative Cube -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineRelativeCube

noncomputable section

/-! The genuine normalized cube identity over every Noetherian affine
base, with its full scheme structure and every test scheme retained. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

namespace Theta.Geometric

variable {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
    {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left)

include P

theorem noetherianAffine_universal_cube :
    Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
      (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A) = 1 := by
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let PC : Projective.ProjectivePresentations.ProjectivePresentation (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A) :=
    (P.product P).product P
  let q := Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
    (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A)
  let C : Line.Bundles.LineBundle (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).left := q.out
  have hC : Line.Bundles.LineBundle.classOf C = q := Quotient.out_eq _
  let z : 𝟙_ (Over S) ⟶ Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A := 1
  have hz : z.left ≫ (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom = 𝟙 S := z.w
  have hr : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback z.left (Line.Bundles.LineBundle.classOf C) = 1 := by
    rw [hC]
    change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback z.left
      (Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
        (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A)) = 1
    rw [Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass_pullback]
    simp only [z, MonObj.one_comp, Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass,
      Picard.ThetaConstruction.RelativeCubeClasses.Geometric.identityNormalizedLine_one_class, mul_one, div_one]
  obtain ⟨e⟩ := Projective.StalkFrames.Theta.Geometric.projective_line_trivial_of_stalk_frames PC
    z.left hz C (Classical.choice (Quotient.exact hr)) (by
      intro x
      let b := S.fromSpecStalk x
      have : IsLocalRing Γ(Spec (S.presheaf.stalk x), ⊤) :=
        RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isLocalRing (S.presheaf.stalk x)
      have : IsNoetherianRing Γ(Spec (S.presheaf.stalk x), ⊤) :=
        RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isNoetherianRing (S.presheaf.stalk x)
      have hx : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom b)
          (Line.Bundles.LineBundle.classOf C) = 1 := by
        rw [hC]
        change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom b)
          (Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
            (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A)) = 1
        rw [Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass_baseChange, IdentityNormalizationBaseChange.Theta.Geometric.identityNormalizedLine_baseChange_class]
        exact Local.RelativeCube.Theta.Geometric.local_cube (A.pullback b) (P.baseChange b)
          (L.pullback (pullback.fst A.scheme.hom b)) _ _ _
      exact Quotient.exact hx)
  exact hC.symm.trans (Quotient.sound ⟨e⟩)

theorem noetherianAffine_cube {U : Over S} (a b c : U ⟶ A.scheme) :
    Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a b c = 1 :=
  Relative.CubeProducts.Theta.Geometric.relativeCubeClass_eq_of_universal A _ (noetherianAffine_universal_cube A P L) a b c

end Theta.Geometric

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineRelativeCube
