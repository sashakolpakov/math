import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalBoundaryTransform

/-! # Canonical Boundary Open Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalBoundaryOpenTransport.Construction

noncomputable section

/-! Every label of the actual canonical blowup boundary commutes with open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalBlowupCanonicalBoundary_comap_open
    {V X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral V] [IsLocallyNoetherian V]
    (j : V ⟶ X) [IsOpenImmersion j] (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (L : V.IdealSheafData) (hL : L ≠ ⊥) (he : I.comap j = L)
    {β : Type} (D : β → X.IdealSheafData) :
    (fun l => (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l).comap
      (GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo j I hI L hL he)) =
      CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary L hL (fun l => (D l).comap j) := by
  funext l
  cases l with
  | none =>
      change (I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)).comap
        (GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo j I hI L hL he) = L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase L hL)
      rw [← Scheme.IdealSheafData.comap_comp, GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo_over,
        Scheme.IdealSheafData.comap_comp, he]
  | some l => exact GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo_controlled j I (D l) hI L hL he 1

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalBoundaryOpenTransport.Construction
