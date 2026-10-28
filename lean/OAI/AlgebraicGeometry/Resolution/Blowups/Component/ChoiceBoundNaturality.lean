import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceBounds
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.BoundOverlap

/-! # Choice Bound Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Component

noncomputable section

/-! Coefficient bounds for terminal-or-normal choices survive étale restriction and normal replacement. -/

universe u

theorem ChoiceBoundNaturality.Construction.relativeCoefficientIdeal_top_of_tangent_top
    (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (z : R) (J : Ideal R) (n : ℕ) (ht : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤) :
    Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J (n + 1) = ⊤ := by
  have h := le_iSup (fun j : Fin (n + 1) =>
    ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val).map (Ideal.Quotient.mk (Ideal.span {z}))) ^
      WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) j) ⟨n, Nat.lt_succ_self n⟩
  change ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (Ideal.Quotient.mk (Ideal.span {z}))) ^
    WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) ⟨n, Nat.lt_succ_self n⟩ ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J (n + 1) at h
  rw [ht, Ideal.map_top, Ideal.top_pow] at h
  exact top_le_iff.mp h

section

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] {J : Ideal R} {n : ℕ}

theorem CenterChoice.Construction.ComponentCenterChoice.hasBound_of_terminal (C : CenterChoice.Construction.ComponentCenterChoice k R J n) (m : ℕ)
    (ht : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤) : C.HasBound m := by
  cases C with
  | terminal _ => trivial
  | normal z D hD hz =>
      have hH : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n = ⊤ := by
        rwa [HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent]
      have hC := ChoiceBoundNaturality.Construction.relativeCoefficientIdeal_top_of_tangent_top k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n hH
      change Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k _ m = ⊤
      have h := Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k
        (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) (Nat.zero_le m)
      change Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ≤ _ at h
      exact top_le_iff.mp (hC ▸ h)

def CenterChoice.Construction.ComponentCenterChoice.mapEtale [Algebra.Smooth k R] (C : CenterChoice.Construction.ComponentCenterChoice k R J n)
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) : CenterChoice.Construction.ComponentCenterChoice k S (J.map f.toRingHom) n := by
  cases C with
  | terminal ht =>
      exact .terminal (by rw [← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf, ht, Ideal.map_top])
  | normal z D hD hz =>
      refine .normal (f z) (Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k f.toRingHom hf f.commutes D) ?_ ?_
      · change Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k f.toRingHom hf f.commutes D (f.toRingHom z) = 1
        rw [Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply, hD, map_one]
      · rw [← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf]
        exact Ideal.mem_map_of_mem _ hz

theorem CenterChoice.Construction.ComponentCenterChoice.hasBound_mapEtale [Algebra.Smooth k R] (C : CenterChoice.Construction.ComponentCenterChoice k R J n)
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) {m : ℕ} (hb : C.HasBound m) :
    (C.mapEtale f hf).HasBound m := by
  cases C with
  | terminal _ => trivial
  | normal z D hD hz =>
      let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
      exact Coefficient.TangentBaseChange.Construction.homogenized_coefficient_bound_map_etale k f hf z J n m hb

end

theorem CenterChoice.Construction.ComponentCenterChoice.hasBound_of_other_choice
    {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra ℚ R] [Algebra.Smooth k R]
    {J : Ideal R} {n m : ℕ} (C B : CenterChoice.Construction.ComponentCenterChoice k R J n) (hb : C.HasBound m) : B.HasBound m := by
  cases C with
  | terminal ht => exact B.hasBound_of_terminal m ht
  | normal z D hD hz =>
      cases B with
      | terminal _ => trivial
      | normal t E hE ht => exact Blowups.Smooth.CoefficientBoundIndependence.Construction.smooth_coefficient_bound_of_other_normal k J n m z t D E hD hE hz ht hb

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Component
