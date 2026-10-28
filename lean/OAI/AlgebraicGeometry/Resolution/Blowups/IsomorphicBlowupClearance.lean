import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Factorization
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialPermissibility
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialSheafRestriction

/-! # Isomorphic Blowup Clearance -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupClearance.Construction

noncomputable section

/-! An isomorphic permissible blowup with a bounded order has no controlled zero along its center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smoothDifferentialIdealSheaf_power_mul_le_sup {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I J : X.IdealSheafData) (b : ℕ) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (I ^ b * J) b ≤ I ⊔ J := by
  have hp : I ^ b * J ≤ (I ⊔ J) ^ (1 + b) := by
    intro U
    change (I.ideal U) ^ b * J.ideal U ≤ (I.ideal U ⊔ J.ideal U) ^ (1 + b)
    rw [Nat.add_comm 1 b, pow_succ]
    exact Ideal.mul_mono (pow_le_pow_left' le_sup_left b) le_sup_right
  have h := Global.DifferentialPermissibility.Construction.smoothDifferentialIdealSheaf_le_pow f (I ⊔ J) (I ^ b * J) 1 b hp
  simpa only [pow_one] using h

theorem globalBlowup_isIso_controlled_sup_center {X : Scheme}
    [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ) [IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)]
    (hperm : J ≤ I ^ b) (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J b = ⊤) :
    I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ⊔ GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b = ⊤ := by
  have h := smoothDifferentialIdealSheaf_power_mul_le_sup (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
    (I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) b
  rw [GlobalControlled.Factorization.Construction.globalBlowup_controlledIdeal_factorization I J hI b hperm,
    ← Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open f J b (GlobalBlowup.Data.Construction.globalBlowupToBase I hI),
    hbound, Scheme.IdealSheafData.comap_top] at h
  exact top_le_iff.mp h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupClearance.Construction
