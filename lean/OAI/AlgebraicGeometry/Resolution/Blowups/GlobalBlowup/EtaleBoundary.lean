import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalColonFlatPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtalePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalBoundaryTransform

/-! # Etale Boundary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtaleBoundary.Construction

noncomputable section

/-! Every controlled ideal and every canonical boundary label commute with the actual étale blowup map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem controlledIdealSheaf_comap_flat
    {X Y Z : Scheme.{0}} [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (I J : X.IdealSheafData) (b : ℕ) (π : Y ⟶ X)
    (hI : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (I.comap π)) (q : Z ⟶ Y) [Flat q] :
    (GlobalControlled.Ideal.Construction.controlledIdealSheaf I J b π).comap q = GlobalControlled.Ideal.Construction.controlledIdealSheaf I J b (q ≫ π) := by
  unfold GlobalControlled.Ideal.Construction.controlledIdealSheaf
  rw [Locally.PrincipalColonFlatPullback.Construction.locallyPrincipal_noetherianIdealSheafColon_comap_flat _ _ (hI.pow b),
    IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp]

theorem globalBlowupMapTo_controlledIdeal_etale
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ X) [Etale q]
    (I J : X.IdealSheafData) (L : Y.IdealSheafData)
    (hq : I.comap q = L) (hI : I ≠ ⊥) (hL : L ≠ ⊥) (b : ℕ) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap (SpecifiedMap.Construction.globalBlowupMapTo q I L hq hI hL) =
      GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal L (J.comap q) hL b := by
  let : Etale (SpecifiedMap.Construction.globalBlowupMapTo q I L hq hI hL) := EtaleMap.Construction.globalBlowupMapTo_etale q I L hq hI hL
  rw [GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal, controlledIdealSheaf_comap_flat I J b _
    (Global.ExceptionalPrincipality.Construction.globalBlowup_center_locallyPrincipal I hI), SpecifiedMap.Construction.globalBlowupMapTo_over]
  unfold GlobalControlled.Ideal.Construction.controlledIdealSheaf GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hq]
  rfl

theorem globalBlowupMapTo_canonicalBoundary_etale
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ X) [Etale q]
    (I : X.IdealSheafData) (L : Y.IdealSheafData)
    (hq : I.comap q = L) (hI : I ≠ ⊥) (hL : L ≠ ⊥)
    {β : Type} (D : β → X.IdealSheafData) (j : Option β) :
    (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D j).comap (SpecifiedMap.Construction.globalBlowupMapTo q I L hq hI hL) =
      CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary L hL (fun k => (D k).comap q) j := by
  cases j with
  | none =>
      change (I.comap (Data.Construction.globalBlowupToBase I hI)).comap _ = L.comap (Data.Construction.globalBlowupToBase L hL)
      rw [← Scheme.IdealSheafData.comap_comp, SpecifiedMap.Construction.globalBlowupMapTo_over,
        Scheme.IdealSheafData.comap_comp, hq]
  | some j => exact globalBlowupMapTo_controlledIdeal_etale q I (D j) L hq hI hL 1

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtaleBoundary.Construction
