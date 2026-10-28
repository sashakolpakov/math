import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceBundle

/-! # Relative Normalization Fibers -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeNormalizationFibers.Geometric

noncomputable section

/-! Identity normalization preserves the actual line bundle on each
field fiber. The comparison is an algebraic sheaf isomorphism obtained
from triviality of the pulled-back identity line over that field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem identityNormalizedLine_fieldPullback_class
    {K : Type} [Field K] {Y : Scheme} (f : Y ⟶ A.scheme.left)
    (ρ : Y ⟶ Spec (.of K)) (b : Spec (.of K) ⟶ S) (h : f ≫ A.scheme.hom = ρ ≫ b) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback f) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback f) := by
  have hz : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (b ≫ η[A.scheme].left) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 :=
    Quotient.sound (RepresentationTheory.Theta.Geometric.LineBundleFieldTriviality.lineBundle_over_field_trivial K (L.pullback (b ≫ η[A.scheme].left)))
  have hb : (f ≫ A.scheme.hom) ≫ η[A.scheme].left = ρ ≫ (b ≫ η[A.scheme].left) :=
    (congrArg (fun t => t ≫ η[A.scheme].left) h).trans (Category.assoc _ _ _)
  change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L *
    (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback A.scheme.hom (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback η[A.scheme].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)))⁻¹) =
      RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
  rw [map_mul, map_inv, RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp, RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp, hb,
    ← RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp, hz, map_one, inv_one, mul_one]

def identityNormalizedLine_fieldFiberIso {K : Type} [Field K] (b : Spec (.of K) ⟶ S) :
    (((RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback (pullback.fst A.scheme.hom b)).sheaf) ≅
      (L.pullback (pullback.fst A.scheme.hom b)).sheaf :=
  Classical.choice (Quotient.exact (identityNormalizedLine_fieldPullback_class A L
    (pullback.fst A.scheme.hom b) (pullback.snd A.scheme.hom b) b pullback.condition))

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeNormalizationFibers.Geometric
