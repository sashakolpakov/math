import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverKernelPairFactor

/-! # Quotient Endomorphism -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientEndomorphism

noncomputable section

/-! A family endomorphism compatible with an actual effective descent
relation descends over the quotient base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem family_quotient_endomorphism_descends {B T X W : Scheme.{0}}
    (u : T ⟶ B) (a : X ⟶ T) (Y : Over B) (q : X ⟶ Y.left)
    [EffectiveEpi q] (hbase : q ≫ Y.hom = a ≫ u)
    (s t : W ⟶ X) (hq : IsKernelPair q s t)
    (m : X ⟶ X) (hm : m ≫ a = a) (r : W ⟶ W)
    (hs : r ≫ s = s ≫ m) (ht : r ≫ t = t ≫ m) :
    ∃! d : Y ⟶ Y, q ≫ d.left = m ≫ q := by
  let X' : Over B := Over.mk (a ≫ u)
  let q' : X' ⟶ Y := Over.homMk q hbase
  have : EffectiveEpi q'.left := inferInstanceAs (EffectiveEpi q)
  let m' : X' ⟶ X' := Over.homMk m (by
    change m ≫ (a ≫ u) = a ≫ u
    rw [← Category.assoc, hm])
  obtain ⟨d, hd, hu⟩ := OverKernelPairFactor.over_endomorphism_descends_of_relation q' s t hq m' r hs ht
  refine ⟨d, congrArg Over.Hom.left hd, ?_⟩
  intro f hf
  exact hu f (Over.OverMorphism.ext hf)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientEndomorphism
