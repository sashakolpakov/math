import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BoundedResolution
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.DimensionBound

/-! # Dimension Bound -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.DimensionBound

noncomputable section

/-! Native Tor vanishing over finite-variable polynomial rings, their
localizations, and flat essentially finite-type unramified extensions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.DimensionBound

theorem tor_isZero_of_bound (R : Type u) [CommRing R] (d : ℕ) (h : Polynomial.DimensionBound.GlobalBound R d)
    (M N : ModuleCat.{u} R) (i : ℕ) (hi : d < i) :
    IsZero (((Tor (ModuleCat R) i).obj M).obj N) := by
  let := h N
  exact BoundedResolution.tor_isZero R M N d i hi

theorem tor_length_zero_of_bound (R : Type u) [CommRing R] (d : ℕ) (h : Polynomial.DimensionBound.GlobalBound R d)
    (M N : ModuleCat.{u} R) (i : ℕ) (hi : d < i) :
    Module.length R (((Tor (ModuleCat R) i).obj M).obj N) = 0 := by
  let := h N
  exact BoundedResolution.tor_length_zero R M N d i hi

theorem polynomial_tor_isZero (K : Type u) [Field K] (n : ℕ)
    (M N : ModuleCat.{u} (MvPolynomial (Fin n) K)) (i : ℕ) (hi : n < i) :
    IsZero (((Tor (ModuleCat (MvPolynomial (Fin n) K)) i).obj M).obj N) :=
  tor_isZero_of_bound _ n (Polynomial.DimensionBound.mvPolynomial_bound K n) M N i hi

theorem etale_polynomial_tor_length_zero (K S : Type u) [Field K] [CommRing S] (n : ℕ)
    [Algebra (MvPolynomial (Fin n) K) S] [Module.Flat (MvPolynomial (Fin n) K) S]
    [Algebra.FormallyUnramified (MvPolynomial (Fin n) K) S]
    [Algebra.EssFiniteType (MvPolynomial (Fin n) K) S]
    (M N : ModuleCat.{u} S) (i : ℕ) (hi : n < i) :
    Module.length S (((Tor (ModuleCat S) i).obj M).obj N) = 0 :=
  tor_length_zero_of_bound S n
    (Etale.DimensionBound.extension_bound (MvPolynomial (Fin n) K) S n
      (Polynomial.DimensionBound.mvPolynomial_bound K n)) M N i hi

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.DimensionBound
