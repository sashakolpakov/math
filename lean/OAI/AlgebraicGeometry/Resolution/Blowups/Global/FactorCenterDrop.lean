import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompanionTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothIntrinsicOrderDrop
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizedTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Identities

/-! # Factor Center Drop -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.FactorCenterDrop.Construction

noncomputable section

/-! Removing one center factor bounds the remaining order locus by the unremoved factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

theorem globalBlowupControlledIdeal_center_product
    (K L : X.IdealSheafData) (hK : K ≠ ⊥) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K (K * L) hK 1 = L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK) := by
  have h := CompanionTransform.Construction.globalBlowup_companion_product_transform K K L hK 0 1 (by omega)
    (by simpa only [Nat.sub_zero, pow_one] using (le_refl K))
    (by simp only [pow_zero, Scheme.IdealSheafData.one_eq_top, le_top])
  rw [Nat.sub_zero, SmoothIntrinsicOrderDrop.Construction.globalBlowupControlledIdeal_center_one, GlobalControlled.Identities.Construction.globalBlowupControlledIdeal_zero,
    ← Scheme.IdealSheafData.one_eq_top, one_mul] at h
  exact h

theorem global_factor_center_differential_bound
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J K L : X.IdealSheafData) (hK : K ≠ ⊥) (n : ℕ)
    [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase K hK ≫ f)]
    (hfactor : K * L ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n) (hperm : J ≤ K ^ (n + 1)) :
    L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK) ≤
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase K hK ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K J hK (n + 1)) n := by
  have hfirst := HomogenizedTransform.Construction.globalBlowupControlledIdeal_mono K hK 1 hfactor
  rw [globalBlowupControlledIdeal_center_product] at hfirst
  have hdiff := DifferentialTransform.Construction.globalBlowup_relativeDifferential_controlled_le f K J hK 1 n
    (by simpa only [Nat.add_comm 1 n] using hperm)
  rw [Nat.add_comm 1 n] at hdiff
  exact hfirst.trans hdiff

theorem global_factor_center_remaining_support
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J K L : X.IdealSheafData) (hK : K ≠ ⊥) (n : ℕ)
    [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase K hK ≫ f)]
    (hfactor : K * L ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n) (hperm : J ≤ K ^ (n + 1)) :
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase K hK ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K J hK (n + 1)) n).support ≤
        L.support.preimage (GlobalBlowup.Data.Construction.globalBlowupToBase K hK).continuous := by
  have h := Scheme.IdealSheafData.support_antitone
    (global_factor_center_differential_bound f J K L hK n hfactor hperm)
  rw [Scheme.IdealSheafData.support_comap] at h
  exact h

theorem global_factor_center_cleared_over_component
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J K L : X.IdealSheafData) (hK : K ≠ ⊥) (n : ℕ)
    [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase K hK ≫ f)]
    (hfactor : K * L ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n) (hperm : J ≤ K ^ (n + 1))
    (hdisjoint : K ⊔ L = ⊤) (x : GlobalBlowup.Data.Construction.globalBlowup K hK)
    (hx : GlobalBlowup.Data.Construction.globalBlowupToBase K hK x ∈ K.support) :
    x ∉ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase K hK ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K J hK (n + 1)) n).support := by
  intro hx'
  have hL := global_factor_center_remaining_support f J K L hK n hfactor hperm hx'
  have hs := congrArg Scheme.IdealSheafData.support hdisjoint
  rw [Scheme.IdealSheafData.support_sup, Scheme.IdealSheafData.support_top] at hs
  have hmem : GlobalBlowup.Data.Construction.globalBlowupToBase K hK x ∈ K.support ⊓ L.support := ⟨hx, hL⟩
  rw [hs] at hmem
  exact hmem

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.FactorCenterDrop.Construction
