import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.IsoImage
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Iso Image -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.IsoImage

noncomputable section

/-! Direct image along a scheme isomorphism preserves quasicoherence by its actual inverse-restriction comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

def modulePushforwardRestrictInverseIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (M : X.Modules) : (pushforward f).obj M ≅ M.restrict (inv f) :=
  ((LineBundle.IsoImage.restrictFunctorInverseIso (asIso f).symm).app ((pushforward f).obj M)).symm ≪≫
    (restrictFunctor (inv f)).mapIso ((restrictFunctorAdjCounitIso f).app M)

theorem modulePushforward_quasicoherent_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (M : X.Modules) [M.IsQuasicoherent] : ((pushforward f).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (modulePushforwardRestrictInverseIso f M).symm inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.IsoImage
