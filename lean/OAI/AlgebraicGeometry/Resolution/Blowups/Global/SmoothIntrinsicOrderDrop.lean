import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceOrderComplement
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialFiltration

/-! # Smooth Intrinsic Order Drop -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothIntrinsicOrderDrop.Construction

noncomputable section

/-! A smooth intrinsic maximal-order center clears its order threshold in one actual blowup, in every dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem controlledIdealSheaf_center_power {Y X : Scheme.{u}} [IsLocallyNoetherian Y]
    (I : X.IdealSheafData) (b : ℕ) (π : Y ⟶ X) : GlobalControlled.Ideal.Construction.controlledIdealSheaf I (I ^ b) b π = ⊤ := by
  unfold GlobalControlled.Ideal.Construction.controlledIdealSheaf
  rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow]
  exact (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon_eq_top_iff _ _).mpr le_rfl

theorem globalBlowupControlledIdeal_center_one
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I I hI 1 = ⊤ := by
  change GlobalControlled.Ideal.Construction.controlledIdealSheaf I I 1 (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) = ⊤
  simpa only [pow_one] using controlledIdealSheaf_center_power I 1 (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)

theorem global_smooth_intrinsic_center_order_drop
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J : X.IdealSheafData) (n : ℕ) (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (hcenter : I = Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n) [Smooth (I.subschemeι ≫ f)] :
    letI : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n = ⊤ := by
  let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI
  have hp : J ≤ I ^ (n + 1) :=
    (SmoothCenterCriterion.Construction.smooth_global_center_order_iff_differentialIdeal f I J n).mpr (by rw [← hcenter])
  have he : 1 + n = n + 1 := Nat.add_comm 1 n
  have h := DifferentialTransform.Construction.globalBlowup_relativeDifferential_controlled_le f I J hI 1 n (he.symm ▸ hp)
  rw [he, ← hcenter, globalBlowupControlledIdeal_center_one] at h
  exact top_le_iff.mp h

theorem exists_global_fixed_control_sequence_of_smooth_intrinsic_center
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J : X.IdealSheafData) (hJ : J ≠ ⊥) (n : ℕ)
    [Smooth ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).subschemeι ≫ f)] :
    Nonempty (MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J) := by
  let I := Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n
  have hI : I ≠ ⊥ := by
    intro h
    have hle := DifferentialFiltration.Construction.smoothDifferentialIdealSheaf_monotone_order f J (Nat.zero_le n)
    rw [Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_zero] at hle
    exact hJ (le_bot_iff.mp (h ▸ hle))
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
  let : Smooth (π ≫ f) := SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI
  have hp : J ≤ I ^ (n + 1) :=
    (SmoothCenterCriterion.Construction.smooth_global_center_order_iff_differentialIdeal f I J n).mpr le_rfl
  have ht := global_smooth_intrinsic_center_order_drop f J n I hI rfl
  refine ⟨.blowup I hI (Nat.succ_pos n) hp inferInstance inferInstance (.terminal ?_)⟩
  simpa only [Nat.add_sub_cancel] using ht

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothIntrinsicOrderDrop.Construction
