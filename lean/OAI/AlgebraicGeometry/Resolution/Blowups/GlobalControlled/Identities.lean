import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Ideal

/-! # Identities -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Identities.Construction

noncomputable section

/-! Terminal and zero-control identities for native global controlled ideals. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem noetherianIdealSheafColon_top_right {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (J : Y.IdealSheafData) : NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon J ⊤ = J := by
  apply Scheme.IdealSheafData.ext
  funext U
  exact Submodule.colon_univ

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]

theorem controlledIdealSheaf_zero (I J : X.IdealSheafData) (π : Y ⟶ X) :
    Ideal.Construction.controlledIdealSheaf I J 0 π = J.comap π := by
  unfold Ideal.Construction.controlledIdealSheaf
  rw [pow_zero, Scheme.IdealSheafData.one_eq_top, noetherianIdealSheafColon_top_right]

theorem controlledIdealSheaf_top (I : X.IdealSheafData) (b : ℕ) (π : Y ⟶ X) :
    Ideal.Construction.controlledIdealSheaf I ⊤ b π = ⊤ := by
  apply top_le_iff.mp
  simpa only [Scheme.IdealSheafData.comap_top] using Ideal.Construction.totalIdeal_le_controlledIdealSheaf I ⊤ b π

variable [IsIntegral X] [IsLocallyNoetherian X]

omit [IsLocallyNoetherian Y] in
theorem globalBlowupControlledIdeal_zero (I J : X.IdealSheafData) (hI : I ≠ ⊥) :
    Ideal.Construction.globalBlowupControlledIdeal I J hI 0 = J.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) :=
  controlledIdealSheaf_zero I J (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)

omit [IsLocallyNoetherian Y] in
theorem globalBlowupControlledIdeal_top (I : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ) :
    Ideal.Construction.globalBlowupControlledIdeal I ⊤ hI b = ⊤ :=
  controlledIdealSheaf_top I b (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Identities.Construction
