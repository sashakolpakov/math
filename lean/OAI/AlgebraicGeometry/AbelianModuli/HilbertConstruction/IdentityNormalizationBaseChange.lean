import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceBundle

/-! # Identity Normalization Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdentityNormalizationBaseChange

noncomputable section

/-! Identity normalization of the original difference-bundle line
commutes with arbitrary base change at the level of actual line classes. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

namespace Theta.Geometric

variable {S T : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (L : Line.Bundles.LineBundle A.scheme.left)

theorem identityNormalizedLine_baseChange_class (b : T ⟶ S) :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst A.scheme.hom b)
      (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) =
    Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine (A.pullback b)
      (L.pullback (pullback.fst A.scheme.hom b))) := by
  let z : T ⟶ pullback A.scheme.hom b := η[(A.pullback b).scheme].left
  have hz : z ≫ pullback.fst A.scheme.hom b =
      b ≫ η[A.scheme].left := by
    change ((Functor.LaxMonoidal.ε (Over.pullback b)).left ≫
      ((Over.pullback b).map η[A.scheme]).left) ≫ pullback.fst A.scheme.hom b = _
    simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc]
    have hu : (Functor.LaxMonoidal.ε (Over.pullback b)).left ≫ pullback.fst (𝟙 S) b = b := by
      have h := pullback.condition (f := 𝟙 S) (g := b)
      simp only [Category.comp_id] at h
      rw [Over.ε_pullback_left, h, IsIso.inv_hom_id_assoc]
    exact congrArg (fun v => v ≫ η[A.scheme].left) hu
  change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst A.scheme.hom b)
      (Line.Bundles.LineBundle.classOf L * (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback A.scheme.hom
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback η[A.scheme].left (Line.Bundles.LineBundle.classOf L)))⁻¹) =
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst A.scheme.hom b) (Line.Bundles.LineBundle.classOf L) *
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.snd A.scheme.hom b)
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback z
          (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst A.scheme.hom b) (Line.Bundles.LineBundle.classOf L))))⁻¹
  rw [map_mul, map_inv]
  congr 2
  rw [RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp, pullback.condition, ← RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp]
  exact congrArg (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.snd A.scheme.hom b))
    ((RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp b η[A.scheme].left (Line.Bundles.LineBundle.classOf L)).trans
      ((congrArg (fun v : T ⟶ A.scheme.left => RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback v (Line.Bundles.LineBundle.classOf L))
        hz.symm).trans
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp z (pullback.fst A.scheme.hom b) (Line.Bundles.LineBundle.classOf L)).symm))

end Theta.Geometric

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdentityNormalizationBaseChange
