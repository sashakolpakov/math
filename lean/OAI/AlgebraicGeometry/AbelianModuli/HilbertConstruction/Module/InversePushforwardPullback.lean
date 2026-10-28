import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.IsoImage

/-! # Inverse Pushforward Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InversePushforwardPullback

noncomputable section

/-! Direct image along the inverse of a scheme isomorphism agrees with its actual module pullback. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

def moduleInversePushforwardPullbackIso {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules) :
    (pushforward e.inv).obj M ≅ (pullback e.hom).obj M :=
  Quasicoherent.IsoImage.modulePushforwardRestrictInverseIso e.inv M ≪≫
    (restrictFunctorCongr (IsIso.inv_eq_of_hom_inv_id e.inv_hom_id)).app M ≪≫
    (restrictFunctorIsoPullback e.hom).app M

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InversePushforwardPullback
