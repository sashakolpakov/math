import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierCenterBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierBlowupEtaleSquare

/-! # Carrier Blowup Pullback Data -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CarrierBlowupPullbackData.Construction

noncomputable section

/-! Pulling back the ambient and coefficient centers constructs their closed-carrier relation and its next cartesian square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem closed_carrier_pullback_geometry
    {X V X' V' : Scheme} (q : V ⟶ X) [IsClosedImmersion q] (q' : V' ⟶ X')
    (p : V' ⟶ V) (a : X' ⟶ X) (hpb : IsPullback p q' q a)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (f' : X' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (h' : V' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (hq : q ≫ f = h) (ha : a ≫ f = f') (hp : p ≫ h = h') :
    IsClosedImmersion q' ∧ q' ≫ f' = h' := by
  refine ⟨MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb inferInstance, ?_⟩
  rw [← ha, ← Category.assoc, ← hpb.w, Category.assoc, hq, hp]

theorem carrier_center_pullback_data
    {X V X' V' : Scheme} (q : V ⟶ X) [IsClosedImmersion q] (q' : V' ⟶ X')
    (p : V' ⟶ V) (a : X' ⟶ X) (hpb : IsPullback p q' q a)
    (I : X.IdealSheafData) (C : V.IdealSheafData) (I' : X'.IdealSheafData) (C' : V'.IdealSheafData)
    (hq : I.comap q = C) (hpush : C.map q = I) (hI : I.comap a = I') (hC : C.comap p = C') :
    I'.comap q' = C' ∧ C'.map q' = I' := by
  constructor
  · rw [← hI, ← Scheme.IdealSheafData.comap_comp, ← hpb.w, Scheme.IdealSheafData.comap_comp, hq, hC]
  · rw [← hC, ← CarrierCenterBaseChange.Construction.idealSheaf_closed_map_comap_of_isPullback q q' p a hpb C, hpush, hI]

theorem exists_carrier_blowup_pullback_data
    {X V X' V' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral V] [IsLocallyNoetherian V]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsIntegral V'] [IsLocallyNoetherian V']
    (q : V ⟶ X) [IsClosedImmersion q] (q' : V' ⟶ X') (p : V' ⟶ V) [Etale p] (a : X' ⟶ X) [Etale a]
    (hpb : IsPullback p q' q a)
    (I : X.IdealSheafData) (C : V.IdealSheafData) (I' : X'.IdealSheafData) (C' : V'.IdealSheafData)
    (hI : I ≠ ⊥) (hC : C ≠ ⊥) (hI' : I' ≠ ⊥) (hC' : C' ≠ ⊥)
    (hqI : I.comap q = C) (hpush : C.map q = I) (heI : I.comap a = I') (heC : C.comap p = C') :
    ∃ hqI' : I'.comap q' = C', C'.map q' = I' ∧
      IsPullback (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo p C C' heC hC hC') (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q' I' C' hqI' hI' hC')
        (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I C hqI hI hC) (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I I' heI hI hI') := by
  obtain ⟨hqI', hpush'⟩ := carrier_center_pullback_data q q' p a hpb I C I' C' hqI hpush heI heC
  exact ⟨hqI', hpush', CarrierBlowupEtaleSquare.Construction.globalBlowupMapTo_carrier_etale_square q q' p a hpb I C I' C'
    hqI hqI' heC heI hI hC hI' hC'⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CarrierBlowupPullbackData.Construction
