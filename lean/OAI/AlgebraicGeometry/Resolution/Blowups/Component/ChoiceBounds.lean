import OAI.AlgebraicGeometry.Resolution.Blowups.Component.CenterChoice
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.TangentCenterChoice

/-! # Choice Bounds -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Component

noncomputable section

/-! Finite coefficient bounds once the canonical component center is the unit ideal. -/

universe u v

section

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {J : Ideal R} {n : ℕ}

def CenterChoice.Construction.ComponentCenterChoice.HasBound (C : CenterChoice.Construction.ComponentCenterChoice k R J n) (m : ℕ) : Prop :=
  match C with
  | .terminal _ => True
  | .normal z _ _ _ => Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) m = ⊤

theorem CenterChoice.Construction.ComponentCenterChoice.hasBound_mono (C : CenterChoice.Construction.ComponentCenterChoice k R J n) {m r : ℕ}
    (hm : C.HasBound m) (hr : m ≤ r) : C.HasBound r := by
  cases C with
  | terminal _ => trivial
  | normal z D hD hz =>
      change Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k _ m = ⊤ at hm
      change Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k _ r = ⊤
      exact top_le_iff.mp (hm ▸ Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k _ hr)

theorem CenterChoice.Construction.ComponentCenterChoice.center_eq_top_of_bound (C : CenterChoice.Construction.ComponentCenterChoice k R J n) {m : ℕ}
    (hm : C.HasBound m) : C.center = ⊤ := by
  cases C with
  | terminal _ => rfl
  | normal z D hD hz =>
      change Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k _ m = ⊤ at hm
      change (DifferentialSaturation.Construction.relativeDifferentialSaturation k _).comap _ = ⊤
      rw [DifferentialSaturation.Construction.relativeDifferentialSaturation_eq_top_of_bound k _ m hm, Ideal.comap_top]

theorem CenterChoice.Construction.ComponentCenterChoice.center_eq_top_iff_exists_bound [IsNoetherianRing R] (C : CenterChoice.Construction.ComponentCenterChoice k R J n) :
    C.center = ⊤ ↔ ∃ m, C.HasBound m := by
  constructor
  · intro hc
    cases C with
    | terminal _ => exact ⟨0, trivial⟩
    | normal z D hD hz =>
        change Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) = ⊤ at hc
        have hsat := Coefficient.ComponentNaturality.Construction.coefficientComponentCenter_quotient k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)
        rw [hc, Ideal.map_top] at hsat
        obtain ⟨m, hm⟩ := DifferentialSaturation.Construction.relativeDifferentialSaturation_eq_iterate k
          (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1))
        exact ⟨m, hm.symm.trans hsat.symm⟩
  · rintro ⟨m, hm⟩
    exact C.center_eq_top_of_bound hm

def CenterChoice.Construction.ComponentCenterChoice.toSurfaceTangentChoice (C : CenterChoice.Construction.ComponentCenterChoice k R J n) (ℓ : ℕ)
    (h : C.HasBound (ℓ + 1)) : Surface.TangentCenterChoice.Construction.SurfaceTangentCenterChoice k R J n ℓ :=
  match C with
  | .terminal ht => .terminal ht
  | .normal z D hD hz => .normal z D hD hz h

end

theorem ChoiceBounds.Construction.exists_uniform_component_choice_bound
    (k : Type u) [CommRing k] {ι : Type v} [Finite ι]
    (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    [∀ i, IsNoetherianRing (R i)] (J : ∀ i, Ideal (R i)) (n : ℕ)
    (C : ∀ i, CenterChoice.Construction.ComponentCenterChoice k (R i) (J i) n) (hc : ∀ i, (C i).center = ⊤) :
    ∃ m, ∀ i, (C i).HasBound m := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose m hm using fun i => ((C i).center_eq_top_iff_exists_bound).mp (hc i)
  refine ⟨Finset.univ.sup m, fun i => (C i).hasBound_mono (hm i) ?_⟩
  exact Finset.le_sup (f := m) (Finset.mem_univ i)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Component
