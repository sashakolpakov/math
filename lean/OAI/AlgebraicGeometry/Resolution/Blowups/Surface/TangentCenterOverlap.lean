import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SurfaceTangentIndependence
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Dimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.DerivationHom

/-! # Tangent Center Overlap -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.TangentCenterOverlap.Construction

noncomputable section

/-! Fixed-level finite-order tangent centers on surface charts agree on every common étale refinement. -/

universe u

theorem surface_coefficient_tangent_centers_agree_on_common_refinement
    (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra k R] [Algebra k A] [Algebra k S] [Algebra ℚ R] [Algebra ℚ A]
    [Algebra.Smooth k R] [Algebra.Smooth k A]
    (f : R →ₐ[k] S) (g : A →ₐ[k] S) (hf : f.toRingHom.Etale) (hg : g.toRingHom.Etale)
    (J : Ideal R) (L : Ideal A) (hJL : J.map f.toRingHom = L.map g.toRingHom)
    (n ℓ : ℕ) (z : R) (t : A) (D : Derivation k R R) (E : Derivation k A A)
    (hD : D z = 1) (hE : E t = 1)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L n)
    (hdim : ringKrullDim R ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1)
    (hboundz : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) (ℓ + 1) = ⊤)
    (hboundt : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k L n) (n + 1)) (ℓ + 1) = ⊤) :
    (Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ).map f.toRingHom =
      (Coefficient.TangentNaturality.Construction.coefficientTangentCenter k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k L n) (n + 1) ℓ).map g.toRingHom := by
  let : Algebra.Smooth k S := Blowups.Etale.RefinementHelpers.Construction.smooth_target_of_etale_algHom k f hf
  let : Algebra ℚ S := ((algebraMap k S).comp (algebraMap ℚ k)).toAlgebra
  let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
  let : Algebra.Smooth k (A ⧸ Ideal.span {t}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one E t hE
  let D' := Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k f.toRingHom hf f.commutes D
  let E' := Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k g.toRingHom hg g.commutes E
  have hD' : D' (f z) = 1 := by
    change Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k f.toRingHom hf f.commutes D (f.toRingHom z) = 1
    rw [Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply, hD, map_one]
  have hE' : E' (g t) = 1 := by
    change Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k g.toRingHom hg g.commutes E (g.toRingHom t) = 1
    rw [Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply, hE, map_one]
  have hz' : f z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map f.toRingHom) n := by
    rw [← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf J n]
    exact Ideal.mem_map_of_mem _ hz
  have ht' : g t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map f.toRingHom) n := by
    rw [hJL, ← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k g hg L n]
    exact Ideal.mem_map_of_mem _ ht
  have hdS : ringKrullDim S ≤ 2 := (Blowups.Etale.Dimension.Construction.ringKrullDim_le_of_etale f.toRingHom hf).trans hdim
  have hbz' := Coefficient.TangentBaseChange.Construction.homogenized_coefficient_bound_map_etale k f hf z J n (ℓ + 1) hboundz
  have hbt' := Coefficient.TangentBaseChange.Construction.homogenized_coefficient_bound_map_etale k g hg t L n (ℓ + 1) hboundt
  rw [← hJL] at hbt'
  rw [Coefficient.TangentBaseChange.Construction.homogenized_coefficientTangentCenter_map_etale k f hf,
    Coefficient.TangentBaseChange.Construction.homogenized_coefficientTangentCenter_map_etale k g hg, ← hJL]
  exact Blowups.Smooth.SurfaceTangentIndependence.Construction.smooth_surface_coefficient_tangent_center_independent_of_normal k
    (J.map f.toRingHom) n ℓ (f z) (g t) D' E' hD' hE' hz' ht' hdS hlevel hbz' hbt'

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.TangentCenterOverlap.Construction
