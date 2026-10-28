import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.GlobalCoefficientEtalePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceCoefficientPersistence
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CarrierBaseChange

/-! # Common Carrier Coefficient Equality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CommonCarrierCoefficientEquality.Construction

noncomputable section

/-! Matching ambient marked ideals give matching intrinsic coefficient ideals on the actual common carrier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smoothCoefficientIdealSheaf_common_carrier
    {X V V' S C : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (d : ℕ)
    (q : V ⟶ X) (q' : V' ⟶ X) (q0 : C ⟶ S)
    (a b : S ⟶ X) [Etale a] [Etale b] (p : C ⟶ V) (p' : C ⟶ V')
    (ha : p ≫ q = q0 ≫ a) (hb : p' ≫ q' = q0 ≫ b)
    (hf : a ≫ f = b ≫ f) (hJ : J.comap a = J.comap b) :
    (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J d q).comap p =
      (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J d q').comap p' := by
  rw [Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothCoefficientIdealSheaf_comap_etale_square f J d q q0 a p ha,
    Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothCoefficientIdealSheaf_comap_etale_square f J d q' q0 b p' hb, hJ]
  exact Global.SequenceCoefficientPersistence.Construction.smoothCoefficientIdealSheaf_structure_congr (a ≫ f) (b ≫ f) hf _ d q0

theorem idealSheaf_common_carrier_pullback
    {X V V' S C : Scheme} (D : X.IdealSheafData)
    (q : V ⟶ X) (q' : V' ⟶ X) (q0 : C ⟶ S)
    (a b : S ⟶ X) (p : C ⟶ V) (p' : C ⟶ V')
    (ha : p ≫ q = q0 ≫ a) (hb : p' ≫ q' = q0 ≫ b)
    (hD : D.comap a = D.comap b) : (D.comap q).comap p = (D.comap q').comap p' := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, ha, hb,
    Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hD]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CommonCarrierCoefficientEquality.Construction
