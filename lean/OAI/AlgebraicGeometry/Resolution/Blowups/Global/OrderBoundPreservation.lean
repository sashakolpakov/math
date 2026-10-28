import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Identities
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Nonzero

/-! # Order Bound Preservation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderBoundPreservation.Construction

noncomputable section

/-! Global order bounds retained under actual permissible smooth-ambient blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]

/-- A permissible controlled transform retains the global differential
order bound whenever its actual ambient blowup is smooth over the original base. -/
theorem globalBlowup_preserves_differential_order_bound
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ)
    [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)] (hperm : J ≤ I ^ b)
    (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J b = ⊤) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) b = ⊤ := by
  have h := DifferentialTransform.Construction.globalBlowup_relativeDifferential_controlled_le f I J hI 0 b
    (by simpa only [Nat.zero_add] using hperm)
  rw [hbound, GlobalControlled.Identities.Construction.globalBlowupControlledIdeal_top] at h
  simpa only [Nat.zero_add] using top_le_iff.mp h

/-- Both induction hypotheses needed for a further step, nonzeroness and
the original differential order bound, hold for the native transformed ideal. -/
theorem globalBlowup_retains_nonzero_and_order_bound
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ) (hJ : J ≠ ⊥)
    [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)] (hperm : J ≤ I ^ b)
    (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J b = ⊤) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b ≠ ⊥ ∧
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) b = ⊤ :=
  ⟨GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot I J hI b hJ,
    globalBlowup_preserves_differential_order_bound f I J hI b hperm hbound⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderBoundPreservation.Construction
