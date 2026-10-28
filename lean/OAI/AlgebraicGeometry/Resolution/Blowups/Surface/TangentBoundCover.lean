import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.SurfaceTangentBoundCover
import OAI.AlgebraicGeometry.Resolution.Blowups.UnitCenterTerminalCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.TangentCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentQuotientCenter

/-! # Tangent Bound Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface

noncomputable section

/-! Every point has an actual étale blowup-generating neighborhood with a smaller coefficient bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem TangentCenterChoice.Construction.SurfaceTangentCenterChoice.exists_pointed_bounded_blowup_generators
    {k R : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing R]
    [Algebra k R] [Algebra ℚ R] [Algebra.Smooth k R]
    {J : Ideal R} {n ℓ : ℕ} (C : TangentCenterChoice.Construction.SurfaceTangentCenterChoice k R J n ℓ)
    (hd : ringKrullDim R ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1) (p : PrimeSpectrum R) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra ℚ S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), f.toRingHom.Etale ∧
      ∃ Q : PrimeSpectrum S, PrimeSpectrum.comap f.toRingHom Q = p ∧
      ∃ (κ : Type u) (g : κ → C.center.map f.toRingHom),
        Ideal.span (Set.range (fun a => (g a).val)) = C.center.map f.toRingHom ∧
        ∀ a, ∃ B : Component.CenterChoice.Construction.ComponentCenterChoice k (Blowup.Charts.Construction.blowupChart (C.center.map f.toRingHom) (g a))
          (ControlledTransform.Construction.blowupControlledTransform (C.center.map f.toRingHom)
            ((Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom) (n + 1) (g a)) n, B.HasBound ℓ := by
  cases C with
  | terminal ht =>
      let f : R →ₐ[k] R := AlgHom.id k R
      have hf : f.toRingHom.Etale := RingHom.Etale.of_bijective Function.bijective_id
      have hJ : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n = ⊤ := by
        rwa [HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent]
      refine ⟨.of R, inferInstance, inferInstance, inferInstance, f, hf, p, rfl, ?_⟩
      apply UnitCenterTerminalCharts.Construction.unit_center_terminal_bounded_generators k _ _ n (n + 1) ℓ
      · exact Ideal.map_top f.toRingHom
      · change Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k ((Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map (RingHom.id R)) n = ⊤
        rw [Ideal.map_id]
        exact hJ
  | normal z D hD hz hb =>
      by_cases hzp : z ∈ p.asIdeal
      · exact Pointed.SurfaceTangentBoundCover.Construction.exists_pointed_normal_tangent_bound_cover k J n ℓ z D hD hz hb hd hlevel p hzp
      · let S := Localization.Away z
        let : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away z
        let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
        let : Algebra.Etale R S := Algebra.Etale.of_isLocalizationAway z
        let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
        have hf : f.toRingHom.Etale := RingHom.etale_algebraMap.mpr inferInstance
        obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime z p hzp
        let I := Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ
        have hzI : z ∈ I := Coefficient.TangentNaturality.Construction.coefficientTangentCenter_normal_mem k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ
        have hI : I.map f.toRingHom = ⊤ := IdempotentQuotientCenter.Construction.center_map_away_member_eq_top I z hzI
        have hL : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k ((Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom) n = ⊤ := by
          rw [← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf, HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent]
          exact IdempotentQuotientCenter.Construction.center_map_away_member_eq_top (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) z hz
        have hc := UnitCenterTerminalCharts.Construction.unit_center_terminal_bounded_generators k (I.map f.toRingHom)
          ((Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom) n (n + 1) ℓ hI hL
        exact ⟨.of S, inferInstance, inferInstance, inferInstance, f, hf, Q, hQ, hc⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface
