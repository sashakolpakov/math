import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.PullbackFaithful
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

/-! # Pullback Faithful -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.PullbackFaithful

noncomputable section

/-!
# Genuine bilinear maps into a line are detected by faithfully flat affine pullback
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
  (M N P : Line.Bundles.LineBundle Y)

/-- Equality of the actual pulled-back bilinear operations implies equality on the quotient. -/
theorem hom_ext (β γ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M.sheaf N.sheaf P.sheaf)
    (h : BilinearPullback.pullback f M.isLine N.isLine β = BilinearPullback.pullback f M.isLine N.isLine γ) : β = γ := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm.injective
  change BilinearPullback.toHom β = BilinearPullback.toHom γ
  apply Line.PullbackFaithful.hom_ext f P
  have he := congrArg BilinearPullback.toHom h
  rw [BilinearPullback.toHom_pullback, BilinearPullback.toHom_pullback] at he
  exact (BilinearPullback.pulledHom_fac f M.isLine N.isLine β).symm.trans
    ((congrArg (fun a => (Tensor.LinePullback.pullbackIso f M.sheaf N.sheaf M.isLine N.isLine).hom ≫ a) he).trans
      (BilinearPullback.pulledHom_fac f M.isLine N.isLine γ))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.PullbackFaithful
