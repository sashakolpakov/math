import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProductTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.CubeAxisClasses
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FieldCube
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Relative Cube -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.RelativeCube

noncomputable section

/-! The original normalized cube identity over a Noetherian local affine
base, including nilpotents. The proof lifts its actual residue frame. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

namespace Theta.Geometric

variable {S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)] [IsNoetherianRing Γ(S, ⊤)]
variable {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
variable (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left)

include P

theorem local_universal_cube :
    Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
      (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A) = 1 := by
  let q := Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
    (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A)
  let C : Line.Bundles.LineBundle (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).left := q.out
  have hC : Line.Bundles.LineBundle.classOf C = q := Quotient.out_eq _
  have hleft : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback
      (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left (A.scheme ⊗ A.scheme).hom A.scheme.hom
        η[A.scheme].left η[A.scheme].w) (Line.Bundles.LineBundle.classOf C) = 1 := by
    rw [hC]
    exact Relative.CubeAxisClasses.Theta.Geometric.relativeCubeClass_left_axis A L
  have hright : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback
      (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right (A.scheme ⊗ A.scheme).hom A.scheme.hom
        η[A.scheme ⊗ A.scheme].left η[A.scheme ⊗ A.scheme].w) (Line.Bundles.LineBundle.classOf C) = 1 := by
    rw [hC]
    exact Relative.CubeAxisClasses.Theta.Geometric.relativeCubeClass_right_axis A L
  let b := ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))
  have hf : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom b)
      (Line.Bundles.LineBundle.classOf C) = 1 := by
    rw [hC]
    change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom b)
      (Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
        (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A)) = 1
    rw [Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass_baseChange]
    exact Projective.FieldCube.Theta.Geometric.projective_field_cube (A.pullback b) (P.baseChange b) _ _ _ _
  obtain ⟨e⟩ := ProductTriviality.localAbelianProduct_line_trivial_of_axes (A.product A) A (P.product P) P
    η[A.scheme ⊗ A.scheme].left η[A.scheme ⊗ A.scheme].w η[A.scheme].left η[A.scheme].w C
    (Classical.choice (Quotient.exact hleft)) (Classical.choice (Quotient.exact hright))
    (Classical.choice (Quotient.exact hf))
  exact hC.symm.trans (Quotient.sound ⟨e⟩)

theorem local_cube {U : Over S} (a b c : U ⟶ A.scheme) :
    Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a b c = 1 :=
  Relative.CubeProducts.Theta.Geometric.relativeCubeClass_eq_of_universal A _ (local_universal_cube A P L) a b c

end Theta.Geometric

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.RelativeCube
