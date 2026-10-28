import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Local
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Factorization
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.IdealSheafProducts

/-! # Principal Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.PrincipalBlowup.Construction

noncomputable section

/-! A nonzero locally principal center has an isomorphic actual global blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalBlowupToBase_isIso_of_locallyPrincipal
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf I) : IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) := by
  have hId : I.comap (𝟙 X) ≠ ⊥ := by rwa [Scheme.IdealSheafData.comap_id]
  have hl : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (I.comap (𝟙 X)) := by rwa [Scheme.IdealSheafData.comap_id]
  let l := GlobalBlowup.Local.Construction.globalBlowupUniversalLift I hI (𝟙 X) hId hl
  have he : l ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = 𝟙 X := GlobalBlowup.Local.Construction.globalBlowupUniversalLift_over I hI (𝟙 X) hId hl
  have hi : GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ l = 𝟙 (GlobalBlowup.Data.Construction.globalBlowup I hI) := by
    apply GlobalBlowup.Local.Construction.globalBlowup_hom_ext I hI (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
      (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot I I hI hI)
    · rw [Category.assoc, he, Category.comp_id]
    · exact Category.id_comp _
  exact ⟨⟨l, hi, he⟩⟩

theorem globalBlowupControlledIdeal_top_center
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (hI : (⊤ : X.IdealSheafData) ≠ ⊥) (b : ℕ) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal ⊤ J hI b = J.comap (GlobalBlowup.Data.Construction.globalBlowupToBase ⊤ hI) := by
  have hp : J ≤ (⊤ : X.IdealSheafData) ^ b := by
    rw [← Scheme.IdealSheafData.one_eq_top, one_pow]
    exact le_top
  have h := GlobalControlled.Factorization.Construction.globalBlowup_controlledIdeal_factorization ⊤ J hI b hp
  rw [Scheme.IdealSheafData.comap_top] at h
  simpa only [← Scheme.IdealSheafData.one_eq_top,
    one_pow, one_mul] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.PrincipalBlowup.Construction
