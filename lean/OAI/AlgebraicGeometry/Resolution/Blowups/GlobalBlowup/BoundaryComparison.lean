import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.SpecifiedMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.AdmissibleMonomialTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedCarrierCenters

/-! # Boundary Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.BoundaryComparison.Construction

noncomputable section

/-! Actual exceptional and retained boundary labels commute with closed-carrier blowup comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalBlowupMap_mixedBoundary
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ X) (I : X.IdealSheafData) (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥)
    {β : Type} (D : β → X.IdealSheafData) (F : Finset β) (hF : ∀ j ∈ F, D j ≤ I) (j : Option β) :
    (Global.MixedBoundary.Construction.globalBlowupMixedBoundary I hI D F j).comap (FunctorialMap.Construction.globalBlowupMap q I hI hY) =
      Global.MixedBoundary.Construction.globalBlowupMixedBoundary (I.comap q) hY (fun j => (D j).comap q) F j := by
  classical
  cases j with
  | none => exact MapControlledIdeal.Construction.globalBlowupMap_totalIdeal q I I hI hY
  | some j =>
      by_cases hj : j ∈ F
      · simp only [Global.MixedBoundary.Construction.globalBlowupMixedBoundary, ite_eq_left hj]
        exact MapControlledIdeal.Construction.globalBlowupMap_controlledIdeal q I (D j) hI hY 1 (by simpa only [pow_one] using hF j hj)
      · simp only [Global.MixedBoundary.Construction.globalBlowupMixedBoundary, ite_eq_right hj]
        exact MapControlledIdeal.Construction.globalBlowupMap_totalIdeal q I (D j) hI hY

theorem globalBlowupMapTo_mixedBoundary
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ X) (I : X.IdealSheafData) (K : Y.IdealSheafData)
    (hq : I.comap q = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥)
    {β : Type} (D : β → X.IdealSheafData) (F : Finset β) (hF : ∀ j ∈ F, D j ≤ I) (j : Option β) :
    (Global.MixedBoundary.Construction.globalBlowupMixedBoundary I hI D F j).comap (SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK) =
      Global.MixedBoundary.Construction.globalBlowupMixedBoundary K hK (fun j => (D j).comap q) F j := by
  subst K
  exact globalBlowupMap_mixedBoundary q I hI hK D F hF j

theorem closedCarrierCenter_boundaryLabels {X Y : Scheme} (q : Y ⟶ X)
    (K : Y.IdealSheafData) {β : Type} [Fintype β] (D : β → X.IdealSheafData) :
    Global.AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels (K.map q) D =
      Global.AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels K (fun j => (D j).comap q) := by
  classical
  ext j
  simp only [Global.AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Scheme.IdealSheafData.le_map_iff_comap_le

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.BoundaryComparison.Construction
