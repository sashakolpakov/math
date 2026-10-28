import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.BaseChange

/-! # Pullback Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Ampleness of a pulled-back line bundle is independent of the actual Cartesian model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Line.Bundles.LineBundle.isAmple_pullback_iff_cartesian
    {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) :
    (L.pullback a).IsAmple ↔ (L.pullback (Limits.pullback.fst f g)).IsAmple := by
  constructor
  · intro hL
    exact (hL.pullback_of_isIso H.isoPullback.inv).of_iso
      ((Scheme.Modules.pullbackComp H.isoPullback.inv a).app L.sheaf ≪≫
        (Scheme.Modules.pullbackCongr H.isoPullback_inv_fst).app L.sheaf)
  · intro hL
    exact (hL.pullback_of_isIso H.isoPullback.hom).of_iso
      ((Scheme.Modules.pullbackComp H.isoPullback.hom (Limits.pullback.fst f g)).app L.sheaf ≪≫
        (Scheme.Modules.pullbackCongr H.isoPullback_hom_fst).app L.sheaf)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
