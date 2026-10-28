import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.Monotonicity
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.EtaleNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.Blowup
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.FiniteBound
import OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupClearance
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderBoundPreservation

/-! # Clearance -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent

noncomputable section

/-! The actual canonical global component step clears all component centers and leaves a finite shared coefficient bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.blowup_center_eq_top (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n)
    (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤)
    (B : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas (GlobalBlowup.Data.Construction.globalBlowupToBase A.center A.center_ne_bot ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal A.center J A.center_ne_bot (n + 1)) n) : B.center = ⊤ := by
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase A.center A.center_ne_bot
  let : IsIso π := A.center_blowup_isIso
  let : CompactSpace (GlobalBlowup.Data.Construction.globalBlowup A.center A.center_ne_bot) :=
    QuasiCompact.compactSpace_of_compactSpace π
  have ht : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (π ≫ f) (J.comap π) (n + 1) = ⊤ := by
    rw [← Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open, hbound, Scheme.IdealSheafData.comap_top]
  obtain ⟨C⟩ := ChoiceAtlas.Construction.exists_global_component_choice_atlas (π ≫ f) (J.comap π) n ht
  have he : A.center.comap π = C.center := A.center_comap_etale π C
  have hC : A.center.comap π ≤ B.center := by
    rw [he]
    exact C.center_mono B (GlobalControlled.Ideal.Construction.totalIdeal_le_controlledIdealSheaf A.center J (n + 1) π)
  have hJ : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal A.center J A.center_ne_bot (n + 1) ≤ B.center := by
    intro U
    exact (B.center_permissible U).trans (Ideal.pow_le_self (Nat.succ_ne_zero n))
  have hs := IsomorphicBlowupClearance.Construction.globalBlowup_isIso_controlled_sup_center f A.center J A.center_ne_bot
    (n + 1) A.center_permissible hbound
  exact top_le_iff.mp (hs ▸ sup_le hC hJ)

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.exists_bounded_atlas_after_component_blowup (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n)
    (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤) :
    ∃ B : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas (GlobalBlowup.Data.Construction.globalBlowupToBase A.center A.center_ne_bot ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal A.center J A.center_ne_bot (n + 1)) n,
      B.center = ⊤ ∧ ∃ m, ∀ i, (B.choice i).HasBound m := by
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase A.center A.center_ne_bot
  let : IsIso π := A.center_blowup_isIso
  let : CompactSpace (GlobalBlowup.Data.Construction.globalBlowup A.center A.center_ne_bot) :=
    QuasiCompact.compactSpace_of_compactSpace π
  have hb := Global.OrderBoundPreservation.Construction.globalBlowup_preserves_differential_order_bound f A.center J A.center_ne_bot
    (n + 1) A.center_permissible hbound
  obtain ⟨B⟩ := ChoiceAtlas.Construction.exists_global_component_choice_atlas (π ≫ f)
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal A.center J A.center_ne_bot (n + 1)) n hb
  have hB := A.blowup_center_eq_top hbound B
  exact ⟨B, hB, B.exists_uniform_bound hB⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent
