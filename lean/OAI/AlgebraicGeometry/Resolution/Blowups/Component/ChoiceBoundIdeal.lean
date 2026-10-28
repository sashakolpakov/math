import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceBoundNaturality

/-! # Choice Bound Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Component

noncomputable section

/-! Unit ideals detecting finite coefficient bounds, with exact étale pullback formulas. -/

universe u

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] {J : Ideal R} {n : ℕ}

def CenterChoice.Construction.ComponentCenterChoice.boundIdeal (C : CenterChoice.Construction.ComponentCenterChoice k R J n) (m : ℕ) : Ideal R :=
  match C with
  | .terminal _ => ⊤
  | .normal z _ _ _ => Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) m

theorem CenterChoice.Construction.ComponentCenterChoice.boundIdeal_eq_top_iff (C : CenterChoice.Construction.ComponentCenterChoice k R J n) (m : ℕ) :
    C.boundIdeal m = ⊤ ↔ C.HasBound m := by
  cases C with
  | terminal _ => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | normal z D hD hz =>
      constructor
      · intro ht
        have he := Coefficient.TangentNaturality.Construction.coefficientTangentCenter_quotient k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) m
        change Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) m = ⊤ at ht
        rw [ht, Ideal.map_top] at he
        exact he.symm
      · intro hb
        change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k _ m).comap _ = ⊤
        rw [hb, Ideal.comap_top]

theorem CenterChoice.Construction.ComponentCenterChoice.boundIdeal_map_etale [Algebra.Smooth k R] (C : CenterChoice.Construction.ComponentCenterChoice k R J n)
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) (m : ℕ) :
    (C.boundIdeal m).map f.toRingHom = (C.mapEtale f hf).boundIdeal m := by
  cases C with
  | terminal _ => exact Ideal.map_top f.toRingHom
  | normal z D hD hz =>
      let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
      exact Coefficient.TangentBaseChange.Construction.homogenized_coefficientTangentCenter_map_etale k f hf z J n m

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Component
