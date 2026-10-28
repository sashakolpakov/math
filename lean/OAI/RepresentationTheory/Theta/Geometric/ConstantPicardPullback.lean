import OAI.RepresentationTheory.Theta.Geometric.Picard.PicardPullback
import OAI.RepresentationTheory.Theta.Geometric.LineBundleFieldTriviality

/-! # Constant Picard Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.ConstantPicardPullback

noncomputable section

/-! A constant map through a field pulls every line class back to the
trivial class, with native scheme pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem picardClass_over_field_eq_one (K : Type) [Field K]
    (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (Spec (.of K))) : a = 1 := by
  refine Quotient.inductionOn a (fun L => ?_)
  exact Quotient.sound (LineBundleFieldTriviality.lineBundle_over_field_trivial K L)

theorem picardPullback_constant {X Y : Scheme} (K : Type) [Field K]
    (f : X ⟶ Spec (.of K)) (p : Spec (.of K) ⟶ Y) (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y) :
    Picard.PicardPullback.picardPullback (f ≫ p) a = 1 := by
  rw [← Picard.PicardPullback.picardPullback_comp, picardClass_over_field_eq_one K (Picard.PicardPullback.picardPullback p a), map_one]

end

end OAI.RepresentationTheory.Theta.Geometric.ConstantPicardPullback
