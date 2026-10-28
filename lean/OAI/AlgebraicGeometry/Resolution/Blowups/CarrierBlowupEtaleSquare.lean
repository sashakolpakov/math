import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtalePullback

/-! # Carrier Blowup Etale Square -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CarrierBlowupEtaleSquare.Construction

noncomputable section

/-! A cartesian comparison of carriers remains cartesian after the corresponding ambient and coefficient blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalBlowupMapTo_carrier_etale_square
    {X Y V W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral V] [IsLocallyNoetherian V]
    [IsIntegral W] [IsLocallyNoetherian W]
    (q : Y ⟶ X) (q' : W ⟶ V) (p : W ⟶ Y) [Etale p] (a : V ⟶ X) [Etale a]
    (hpb : IsPullback p q' q a)
    (I : X.IdealSheafData) (K : Y.IdealSheafData) (I' : V.IdealSheafData) (K' : W.IdealSheafData)
    (hq : I.comap q = K) (hq' : I'.comap q' = K') (hp : K.comap p = K') (ha : I.comap a = I')
    (hI : I ≠ ⊥) (hK : K ≠ ⊥) (hI' : I' ≠ ⊥) (hK' : K' ≠ ⊥) :
    IsPullback (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo p K K' hp hK hK') (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q' I' K' hq' hI' hK')
      (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK) (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I I' ha hI hI') := by
  let u := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo p K K' hp hK hK'
  let v := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I I' ha hI hI'
  let r := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK
  let r' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q' I' K' hq' hI' hK'
  have he : I.comap (q' ≫ a) = K' := by
    rw [Scheme.IdealSheafData.comap_comp, ha, hq']
  have hleft : u ≫ r = GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo (q' ≫ a) I K' he hI hK' := by
    apply GlobalBlowup.MapComposition.Construction.globalBlowupMapTo_unique
    rw [Category.assoc, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over, ← Category.assoc, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over, Category.assoc, hpb.w]
  have hright : r' ≫ v = GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo (q' ≫ a) I K' he hI hK' :=
    GlobalBlowup.MapComposition.Construction.globalBlowupMapTo_comp a q' I I' K' ha hq' he hI hI' hK'
  have houter := (GlobalBlowup.EtalePullback.Construction.globalBlowupMapTo_etale_isPullback p K K' hp hK hK').paste_vert hpb
  have houter' : IsPullback u (r' ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I' hI') (r ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) a := by
    rw [GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over]
    exact houter
  exact houter'.of_bot (hleft.trans hright.symm) (GlobalBlowup.EtalePullback.Construction.globalBlowupMapTo_etale_isPullback a I I' ha hI hI')

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CarrierBlowupEtaleSquare.Construction
