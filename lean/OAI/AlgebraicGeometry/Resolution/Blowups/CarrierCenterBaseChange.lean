import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedCarrierCenters

/-! # Carrier Center Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CarrierCenterBaseChange.Construction

noncomputable section

/-! Pushing a center through a closed carrier commutes with an actual cartesian change of ambient scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem idealSheaf_closed_map_comap_of_isPullback
    {X Y V W : Scheme} (q : Y ⟶ X) [IsClosedImmersion q] (q' : W ⟶ V)
    (p : W ⟶ Y) (a : V ⟶ X) (hpb : IsPullback p q' q a) (J : Y.IdealSheafData) :
    (J.map q).comap a = (J.comap p).map q' := by
  let α := pullback.fst p J.subschemeι
  let γ := pullback.snd p J.subschemeι
  have h1 := IsPullback.of_hasPullback p J.subschemeι
  have houter : IsPullback (α ≫ q') γ a (J.subschemeι ≫ q) := (h1.flip.paste_vert hpb).flip
  have he := ClosedCarrierCenters.Construction.kernel_comap_of_closed_pullback (J.subschemeι ≫ q) (α ≫ q') γ a houter
  change (J.map q).comap a = α.ker.map q'
  simpa only [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι] using he

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CarrierCenterBaseChange.Construction
