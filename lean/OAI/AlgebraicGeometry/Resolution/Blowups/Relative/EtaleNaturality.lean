import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.HomogenizationBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizationTangent
import Mathlib.RingTheory.RingHom.Etale

/-! # Etale Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.EtaleNaturality.Construction

noncomputable section

/-! Intrinsic relative differential ideals under arbitrary étale comparison maps. -/

variable {σ k R S : Type*} [Field k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra (MvPolynomial σ k) R]
  [Algebra.Etale (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) R]
  [Fintype σ] [DecidableEq σ]

include σ in
/-- The target coordinate presentation is induced by the given étale map;
it need not be supplied as additional data. -/
theorem relativeDifferentialIdeal_map_etale (f : R →ₐ[k] S) (hf : f.toRingHom.Etale)
    (J : Ideal R) (n : ℕ) :
    (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom =
      DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map f.toRingHom) n := by
  let P := MvPolynomial σ k
  let : Algebra R S := f.toRingHom.toAlgebra
  let : Algebra.Etale R S := hf
  let : Algebra P S := (f.toRingHom.comp (algebraMap P R)).toAlgebra
  let : IsScalarTower P R S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap k S a = f (algebraMap k R a)
    exact (f.commutes a).symm)
  let : IsScalarTower k P S := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap k S a = f (algebraMap P R (algebraMap k P a))
    rw [← IsScalarTower.algebraMap_apply k P R, f.commutes])
  let : Algebra.Etale P S := Algebra.Etale.comp P R S
  exact DifferentialBaseChange.Construction.etale_iteratedRelativeDifferentialIdeal_baseChange (σ := σ) J n

include σ in
theorem relativeHomogenizedIdeal_map_etale (f : R →ₐ[k] S) (hf : f.toRingHom.Etale)
    (J : Ideal R) (n : ℕ) :
    (DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom =
      DifferentialEquiv.Construction.relativeHomogenizedIdeal k (J.map f.toRingHom) n := by
  unfold DifferentialEquiv.Construction.relativeHomogenizedIdeal
  simp only [Ideal.map_iSup, Ideal.map_mul, Ideal.map_pow,
    relativeDifferentialIdeal_map_etale (σ := σ) f hf]

include σ in
/-- Equality of the homogenized ideals on the comparison chart forces
equality of the full mapped tangent ideals there. -/
theorem etale_homogenized_comparison_tangent_eq
    (f g : R →ₐ[k] S) (hf : f.toRingHom.Etale) (hg : g.toRingHom.Etale)
    (J : Ideal R) (n : ℕ)
    (hH : (DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom =
      (DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map g.toRingHom) :
    (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom =
      (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map g.toRingHom := by
  have hF := relativeDifferentialIdeal_map_etale (σ := σ) f hf (DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n
  have hG := relativeDifferentialIdeal_map_etale (σ := σ) g hg (DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n
  rw [HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent] at hF hG
  rw [hF, hG, hH]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.EtaleNaturality.Construction
