import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.TangentCenterChoice
import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceBoundNaturality

/-! # Choice Etale Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface

noncomputable section

/-! Exact étale transport of the finite-level surface center choice. -/

universe u

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra.Smooth k R] {J : Ideal R} {n ℓ : ℕ}

def TangentCenterChoice.Construction.SurfaceTangentCenterChoice.mapEtale (C : TangentCenterChoice.Construction.SurfaceTangentCenterChoice k R J n ℓ)
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) : TangentCenterChoice.Construction.SurfaceTangentCenterChoice k S (J.map f.toRingHom) n ℓ := by
  cases C with
  | terminal ht =>
      exact .terminal (by rw [← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf, ht, Ideal.map_top])
  | normal z D hD hz hb =>
      let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
      refine .normal (f z) (Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k f.toRingHom hf f.commutes D) ?_ ?_
        (Coefficient.TangentBaseChange.Construction.homogenized_coefficient_bound_map_etale k f hf z J n (ℓ + 1) hb)
      · change Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k f.toRingHom hf f.commutes D (f.toRingHom z) = 1
        rw [Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply, hD, map_one]
      · rw [← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf]
        exact Ideal.mem_map_of_mem _ hz

theorem TangentCenterChoice.Construction.SurfaceTangentCenterChoice.center_map_etale (C : TangentCenterChoice.Construction.SurfaceTangentCenterChoice k R J n ℓ)
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) :
    (C.mapEtale f hf).center = C.center.map f.toRingHom := by
  cases C with
  | terminal _ => exact (Ideal.map_top f.toRingHom).symm
  | normal z D hD _ _ =>
      let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
      exact (Coefficient.TangentBaseChange.Construction.homogenized_coefficientTangentCenter_map_etale k f hf z J n ℓ).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface
