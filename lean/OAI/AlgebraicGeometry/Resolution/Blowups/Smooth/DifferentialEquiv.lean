import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialNaturality
import Mathlib.RingTheory.RingHom.Etale

/-! # Differential Equiv -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialEquiv.Construction

noncomputable section

/-! Intrinsic differential ideals under isomorphisms preserving the coefficient algebra. -/

variable (k : Type*) {R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra.Smooth k R]

/-- Differential ideals commute with an algebra isomorphism, expressed in
the inverse-image convention used by native open pullback of ideal sheaves. -/
theorem smooth_relativeDifferentialIdeal_comap_equiv (e : R ≃ₐ[k] S) (J : Ideal R) (n : ℕ) :
    (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).comap e.symm.toRingHom =
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.comap e.symm.toRingHom) n := by
  let : Algebra R S := e.toRingHom.toAlgebra
  let : Algebra.Etale R S := RingHom.Etale.of_bijective e.bijective
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro c
    exact (e.commutes c).symm)
  have h := DifferentialNaturality.Construction.smooth_iteratedRelativeDifferentialIdeal_baseChange k (S := S) J n
  change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map e.toRingEquiv.toRingHom =
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map e.toRingEquiv.toRingHom) n at h
  have hleft : (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map e.toRingHom =
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).comap e.symm.toRingHom :=
    Ideal.map_comap_of_equiv e.toRingEquiv
  have hright : J.map e.toRingHom = J.comap e.symm.toRingHom :=
    Ideal.map_comap_of_equiv e.toRingEquiv
  exact hleft.symm.trans (h.trans (congrArg (fun L : Ideal S =>
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L n) hright))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialEquiv.Construction
