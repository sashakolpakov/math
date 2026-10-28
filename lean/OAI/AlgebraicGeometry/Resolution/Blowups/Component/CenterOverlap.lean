import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ComponentIndependence
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.DerivationHom

/-! # Center Overlap -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Component.CenterOverlap.Construction

noncomputable section

/-! Independently presented smooth affine charts select the same actual component center on a common refinement. -/

universe u

theorem coefficient_component_centers_agree_on_common_refinement
    (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra k R] [Algebra k A] [Algebra k S] [Algebra ℚ R] [Algebra ℚ A]
    [Algebra.Smooth k R] [Algebra.Smooth k A]
    (f : R →ₐ[k] S) (g : A →ₐ[k] S) (hf : f.toRingHom.Etale) (hg : g.toRingHom.Etale)
    (J : Ideal R) (L : Ideal A) (hJL : J.map f.toRingHom = L.map g.toRingHom)
    (n : ℕ) (z : R) (t : A) (D : Derivation k R R) (E : Derivation k A A)
    (hD : D z = 1) (hE : E t = 1)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L n) :
    (Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)).map f.toRingHom =
      (Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k L n) (n + 1)).map g.toRingHom := by
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
  rw [Coefficient.ComponentBaseChange.Construction.homogenized_coefficientComponentCenter_map_etale k f hf,
    Coefficient.ComponentBaseChange.Construction.homogenized_coefficientComponentCenter_map_etale k g hg, ← hJL]
  exact Blowups.Smooth.ComponentIndependence.Construction.smooth_coefficient_component_center_independent_of_normal k
    (J.map f.toRingHom) n (f z) (g t) D' E' hD' hE' hz' ht'

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Component.CenterOverlap.Construction
