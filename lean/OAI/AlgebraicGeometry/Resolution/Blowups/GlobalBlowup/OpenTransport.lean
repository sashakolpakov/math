import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderLocusPreservation

/-! # Open Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenTransport.Construction

noncomputable section

/-! Specified local centers and controlled ideals in the actual open blowup square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {V X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [IsIntegral V] [IsLocallyNoetherian V]
  (j : V ⟶ X) [IsOpenImmersion j]

def globalBlowupOpenMapTo (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (L : V.IdealSheafData) (hL : L ≠ ⊥) (he : I.comap j = L) :
    Data.Construction.globalBlowup L hL ⟶ Data.Construction.globalBlowup I hI := by
  subst L
  exact OpenMap.Construction.globalBlowupOpenMap j I hI hL

instance globalBlowupOpenMapTo_isOpenImmersion (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (L : V.IdealSheafData) (hL : L ≠ ⊥) (he : I.comap j = L) :
    IsOpenImmersion (globalBlowupOpenMapTo j I hI L hL he) := by
  subst L
  exact OpenMap.Construction.globalBlowupOpenMap_isOpenImmersion j I hI hL

theorem globalBlowupOpenMapTo_over (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (L : V.IdealSheafData) (hL : L ≠ ⊥) (he : I.comap j = L) :
    globalBlowupOpenMapTo j I hI L hL he ≫ Data.Construction.globalBlowupToBase I hI =
      Data.Construction.globalBlowupToBase L hL ≫ j := by
  subst L
  exact OpenMap.Construction.globalBlowupOpenMap_over j I hI hL

theorem globalBlowupOpenMapTo_isPullback (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (L : V.IdealSheafData) (hL : L ≠ ⊥) (he : I.comap j = L) :
    IsPullback (globalBlowupOpenMapTo j I hI L hL he) (Data.Construction.globalBlowupToBase L hL)
      (Data.Construction.globalBlowupToBase I hI) j := by
  subst L
  exact OpenMap.Construction.globalBlowupOpenMap_isPullback j I hI hL

theorem globalBlowupOpenMapTo_controlled (I J : X.IdealSheafData) (hI : I ≠ ⊥)
    (L : V.IdealSheafData) (hL : L ≠ ⊥) (he : I.comap j = L) (b : ℕ) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap (globalBlowupOpenMapTo j I hI L hL he) =
      GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal L (J.comap j) hL b := by
  rw [GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal, GlobalControlled.Ideal.Construction.controlledIdealSheaf_comap_open,
    globalBlowupOpenMapTo_over]
  unfold GlobalControlled.Ideal.Construction.controlledIdealSheaf GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, he]
  rfl

theorem globalBlowupOpenMapTo_range (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (L : V.IdealSheafData) (hL : L ≠ ⊥) (he : I.comap j = L) :
    Set.range (globalBlowupOpenMapTo j I hI L hL he) =
      Data.Construction.globalBlowupToBase I hI ⁻¹' Set.range j := by
  exact congrArg (fun U : (Data.Construction.globalBlowup I hI).Opens => (U : Set (Data.Construction.globalBlowup I hI)))
    (SupportedBlowupSmoothGluing.Construction.opensRange_of_open_pullback (globalBlowupOpenMapTo j I hI L hL he)
      (Data.Construction.globalBlowupToBase L hL) (Data.Construction.globalBlowupToBase I hI) j
      (globalBlowupOpenMapTo_isPullback j I hI L hL he))

theorem globalBlowupOpenMapTo_contains_order_support
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I J : X.IdealSheafData) (hI : I ≠ ⊥)
    (L : V.IdealSheafData) (hL : L ≠ ⊥) (he : I.comap j = L)
    (b : ℕ) (hb : 0 < b) (hp : J ≤ I ^ b) [Smooth (Data.Construction.globalBlowupToBase I hI ≫ f)]
    (hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support : Set X) ⊆ Set.range j) :
    ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) (b - 1)).support : Set (Data.Construction.globalBlowup I hI)) ⊆
      Set.range (globalBlowupOpenMapTo j I hI L hL he) := by
  rw [globalBlowupOpenMapTo_range]
  intro x hx
  apply hcover
  by_contra hn
  exact Global.OrderLocusPreservation.Construction.globalBlowup_orderComplement_preimage_le f I J hI b hb hp hn hx

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenTransport.Construction
