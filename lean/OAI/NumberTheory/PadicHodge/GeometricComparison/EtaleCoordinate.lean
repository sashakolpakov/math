import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Etale Coordinate -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.EtaleCoordinate.EtaleCoordinateBaseEquiv

noncomputable section

/-! An actual coefficient-ring equivalence transports étale polynomial
coordinates while preserving the induced base algebra. -/

universe u
variable (R S A σ : Type u)
  [CommRing R] [CommRing S] [CommRing A] [Algebra S A]
  [Algebra (MvPolynomial σ S) A] [IsScalarTower S (MvPolynomial σ S) A]
  (e : R ≃+* S)

@[instance_reducible]
def baseAlgebra : Algebra R A := ((algebraMap S A).comp e.toRingHom).toAlgebra

@[instance_reducible]
def polynomialAlgebra : Algebra (MvPolynomial σ R) A :=
  ((algebraMap (MvPolynomial σ S) A).comp (MvPolynomial.mapEquiv σ e).toRingHom).toAlgebra

theorem scalarTower : letI := baseAlgebra R S A e
    letI := polynomialAlgebra R S A σ e
    IsScalarTower R (MvPolynomial σ R) A := by
  let := baseAlgebra R S A e
  let := polynomialAlgebra R S A σ e
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap S A (e r) = algebraMap (MvPolynomial σ S) A
    ((MvPolynomial.mapEquiv σ e) (MvPolynomial.C r))
  rw [MvPolynomial.mapEquiv_apply, MvPolynomial.map_C]
  exact IsScalarTower.algebraMap_apply S (MvPolynomial σ S) A (e r)

variable [Algebra.Etale (MvPolynomial σ S) A]

omit [Algebra S A] [IsScalarTower S (MvPolynomial σ S) A] in
theorem etale : letI := polynomialAlgebra R S A σ e
    Algebra.Etale (MvPolynomial σ R) A := by
  let := polynomialAlgebra R S A σ e
  apply RingHom.etale_algebraMap.mp
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (MvPolynomial.mapEquiv σ e).bijective)
    (RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale (MvPolynomial σ S) A)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.EtaleCoordinate.EtaleCoordinateBaseEquiv
