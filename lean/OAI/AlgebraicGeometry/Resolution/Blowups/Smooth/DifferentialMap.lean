import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialNaturality
import Mathlib.RingTheory.RingHom.Etale

/-! # Differential Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialMap.Construction

noncomputable section

/-! Explicit relative differential compatibility for algebra homomorphisms. -/

variable (k : Type*) {R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra.Smooth k R]

theorem smooth_iteratedRelativeDifferentialIdeal_map
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) (J : Ideal R) (n : ℕ) :
    (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom =
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map f.toRingHom) n := by
  let : Algebra R S := f.toRingHom.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp hf
  exact DifferentialNaturality.Construction.smooth_iteratedRelativeDifferentialIdeal_baseChange k J n

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialMap.Construction
