import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierCenterBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierBlowupEtaleSquare
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtaleBoundary

/-! # Carrier Blowup Comparison Data -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CarrierBlowupComparisonData.Construction

noncomputable section

/-! The geometric data for the next ambient and carrier comparison, packaged before recursion on prefixes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_carrier_blowup_comparison_data
    {X V X' V' : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral V] [IsLocallyNoetherian V]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsIntegral V'] [IsLocallyNoetherian V']
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (f' : X' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (J : X.IdealSheafData) (J' : X'.IdealSheafData) (b : ℕ)
    (q : V ⟶ X) [IsClosedImmersion q] (q' : V' ⟶ X') (p : V' ⟶ V) [Etale p] (a : X' ⟶ X) [Etale a]
    (hf : a ≫ f = f') (hJ : J.comap a = J') (hpb : IsPullback p q' q a)
    (I : X.IdealSheafData) (C : V.IdealSheafData) (I' : X'.IdealSheafData) (C' : V'.IdealSheafData)
    (hI : I ≠ ⊥) (hC : C ≠ ⊥) (hI' : I' ≠ ⊥) (hC' : C' ≠ ⊥)
    (hqI : I.comap q = C) (hpush : C.map q = I) (hqI' : I'.comap q' = C') (hpush' : C'.map q' = I')
    (heC : C.comap p = C') :
    ∃ heI : I.comap a = I', Etale (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I I' heI hI hI') ∧
      GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I I' heI hI hI' ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) = GlobalBlowup.Data.Construction.globalBlowupToBase I' hI' ≫ f' ∧
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I I' heI hI hI') =
        GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I' J' hI' b ∧
      IsPullback (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo p C C' heC hC hC') (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q' I' C' hqI' hI' hC')
        (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I C hqI hI hC) (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I I' heI hI hI') := by
  have heI : I.comap a = I' := by
    rw [← hpush, CarrierCenterBaseChange.Construction.idealSheaf_closed_map_comap_of_isPullback q q' p a hpb C, heC, hpush']
  refine ⟨heI, GlobalBlowup.EtaleMap.Construction.globalBlowupMapTo_etale a I I' heI hI hI', ?_, ?_, ?_⟩
  · rw [← Category.assoc, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over, Category.assoc, hf]
  · rw [GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_controlledIdeal_etale, hJ]
  · exact CarrierBlowupEtaleSquare.Construction.globalBlowupMapTo_carrier_etale_square q q' p a hpb I C I' C' hqI hqI' heC heI hI hC hI' hC'

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CarrierBlowupComparisonData.Construction
