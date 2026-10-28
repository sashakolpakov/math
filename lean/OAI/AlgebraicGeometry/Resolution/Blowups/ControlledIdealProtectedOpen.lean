import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Identities
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Complement

/-! # Controlled Ideal Protected Open -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ControlledIdealProtectedOpen.Construction

noncomputable section

/-! A center empty on the protected open leaves its actual open model and marked ideal unchanged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalBlowup_isIso_on_open_of_comap_top
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (C : X.IdealSheafData) (hC : C ≠ ⊥) (O : X.Opens) (hO : C.comap O.ι = ⊤) :
    IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ∣_ O) := by
  apply Blowup.Complement.Construction.globalBlowup_isIso_on_open C hC
  intro x hx hmem
  have hy : (⟨x, hx⟩ : O) ∈ (C.comap O.ι).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hmem
  rw [hO, Scheme.IdealSheafData.support_top] at hy
  exact hy

theorem globalBlowupControlledIdeal_restrict_of_comap_top
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (C J : X.IdealSheafData) (hC : C ≠ ⊥) (b : ℕ) (O : X.Opens) (hO : C.comap O.ι = ⊤) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J hC b).comap (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ⁻¹ᵁ O).ι =
      (J.comap O.ι).comap (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ∣_ O) := by
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase C hC
  let : IsLocallyNoetherian (π ⁻¹ᵁ O).toScheme := LocallyOfFiniteType.isLocallyNoetherian (π ⁻¹ᵁ O).ι
  have hcenter : C.comap ((π ⁻¹ᵁ O).ι ≫ π) = ⊤ := by
    rw [← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp, hO, Scheme.IdealSheafData.comap_top]
  change (GlobalControlled.Ideal.Construction.controlledIdealSheaf C J b π).comap (π ⁻¹ᵁ O).ι = _
  rw [GlobalControlled.Ideal.Construction.controlledIdealSheaf_comap_open, GlobalControlled.Ideal.Construction.controlledIdealSheaf, hcenter,
    ← Scheme.IdealSheafData.one_eq_top, one_pow, Scheme.IdealSheafData.one_eq_top,
    GlobalControlled.Identities.Construction.noetherianIdealSheafColon_top_right, ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ControlledIdealProtectedOpen.Construction
