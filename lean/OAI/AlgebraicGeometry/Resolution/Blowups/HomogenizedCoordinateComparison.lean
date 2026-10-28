import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.ShiftBranch
import OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizationIdempotence

/-! # Homogenized Coordinate Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizedCoordinateComparison.Construction

noncomputable section

/-! Comparing the whole homogenized ideal across changed coordinate charts. -/

variable {σ k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra ℚ R] [Algebra ℚ S]
  [Algebra (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) R]
  [Algebra.FormallyUnramified (MvPolynomial σ k) R] [DecidableEq σ]

theorem etale_coordinate_shift_homogenized_le (D : Derivation k R R)
    (f g : R →ₐ[k] S) (J : Ideal R) (i : σ) (t : S) (n : ℕ)
    (hD : ∀ j : σ, D (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
      if i = j then 1 else 0)
    (hcoords : ∀ j : σ, g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
      f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) +
        if i = j then t else 0)
    (hred : ∀ x : R, g x - f x ∈ Ideal.span {t})
    (hT : t ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom) :
    (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map g.toRingHom ≤
      (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom := by
  have hT' : t ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n).map f.toRingHom := by
    rwa [HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent]
  have h := Etale.HomogenizationComparison.Construction.etale_coordinate_shift_ideal_le_homogenized D f g
    (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) i t n hD hcoords hred hT'
  rwa [HomogenizationIdempotence.Construction.relativeHomogenizedIdeal_idempotent] at h

variable [Algebra.EssFiniteType (MvPolynomial σ k) R]

theorem etale_coordinate_shift_homogenized_neighborhood (D : Derivation k R R)
    (f g : R →ₐ[k] S) (J : Ideal R) (i : σ) (t : S) (n : ℕ)
    (hD : ∀ j : σ, D (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
      if i = j then 1 else 0)
    (hcoords : ∀ j : σ, g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
      f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) +
        if i = j then t else 0)
    (q : Ideal S) [q.IsPrime] (htq : t ∈ q)
    (hq : ∀ x : R, g x - f x ∈ q)
    (hT : t ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom) :
    ∃ s : S, s ∉ q ∧
      ((Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map g.toRingHom).map
          (algebraMap S (Localization.Away s)) ≤
        ((Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom).map
          (algebraMap S (Localization.Away s)) := by
  have hT' : t ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n).map f.toRingHom := by
    rwa [HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent]
  have h := Coordinate.ShiftBranch.Construction.etale_coordinate_shift_homogenization_neighborhood D f g
    (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) i t n hD hcoords q htq hq hT'
  simpa only [HomogenizationIdempotence.Construction.relativeHomogenizedIdeal_idempotent] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizedCoordinateComparison.Construction
