import OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentBlowupCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceBoundIdeal

/-! # Unit Center Terminal Charts -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.UnitCenterTerminalCharts.Construction

noncomputable section

/-! Actual charts over a unit center preserve the terminal differential condition. -/

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem unit_center_controlled_terminal
    (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    (J : Ideal R) (n b : ℕ) (hJ : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤)
    (a : (⊤ : Ideal R)) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform ⊤ J b a) n = ⊤ := by
  have hI : IsIdempotentElem (⊤ : Ideal R) := by simp [IsIdempotentElem]
  rw [IdempotentBlowupCharts.Construction.idempotent_blowup_controlledTransform ⊤ J hI a b]
  let φ : R →ₐ[k] Blowup.Charts.Construction.blowupChart ⊤ a :=
    { __ := Blowup.Charts.Construction.blowupChartConstants ⊤ a, commutes' := fun _ => rfl }
  have hf : φ.toRingHom.Etale := IdempotentBlowupCharts.Construction.idempotent_blowupChartConstants_etale ⊤ hI a
  rw [← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k φ hf, hJ, Ideal.map_top]

theorem unit_center_terminal_bounded_generators
    (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    (I J : Ideal R) (n b m : ℕ) (hI : I = ⊤) (hJ : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤) :
    ∃ (κ : Type u) (g : κ → I), Ideal.span (Set.range (fun a => (g a).val)) = I ∧
      ∀ a, ∃ B : Component.CenterChoice.Construction.ComponentCenterChoice k (Blowup.Charts.Construction.blowupChart I (g a))
        (ControlledTransform.Construction.blowupControlledTransform I J b (g a)) n, B.HasBound m := by
  subst I
  refine ⟨(⊤ : Ideal R), id, ?_, ?_⟩
  · change Ideal.span (Set.range (Subtype.val : (⊤ : Ideal R) → R)) = ⊤
    rw [Subtype.range_val, Ideal.span_eq]
  · intro a
    exact ⟨.terminal (unit_center_controlled_terminal k J n b hJ a), trivial⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.UnitCenterTerminalCharts.Construction
