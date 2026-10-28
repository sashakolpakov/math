import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.BaseChange
import Mathlib.AlgebraicGeometry.Restrict

/-! # Image Ampleness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.ImageAmpleness

noncomputable section

/-! Ampleness on a nested open restriction is ampleness on its actual
open image in the original scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isAmple_on_open_image
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (V : Y.Opens)
    (hL : ((L.pullback j).pullback V.ι).IsAmple) :
    (L.pullback (j ''ᵁ V).ι).IsAmple := by
  have h : (L.pullback (V.ι ≫ j)).IsAmple :=
    hL.of_iso ((Scheme.Modules.pullbackComp V.ι j).app L.sheaf)
  let e : ((L.pullback (V.ι ≫ j)).pullback (j.isoImage V).inv).sheaf ≅
      (L.pullback (j ''ᵁ V).ι).sheaf :=
    (Scheme.Modules.pullbackComp (j.isoImage V).inv (V.ι ≫ j)).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (j.isoImage_inv_ι V)).app L.sheaf
  exact (h.pullback_of_isIso (j.isoImage V).inv).of_iso e

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.ImageAmpleness
