import OAI.AlgebraicGeometry.Resolution.Blowups.TaylorCongruence
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Taylor Shift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TaylorShift.Construction

noncomputable section

/-! Finite Taylor comparison for an actual change of one étale coordinate. -/

variable {σ k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra ℚ R] [Algebra ℚ S]
  [Algebra (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) R]
  [Algebra.FormallyUnramified (MvPolynomial σ k) R] [DecidableEq σ]

/-- Coordinate values and the selected branch modulo the displacement determine
the finite Taylor map on the whole étale algebra. -/
theorem etale_coordinate_shift_eq_taylor (D : Derivation k R R)
    (f g : R →ₐ[k] S) (i : σ) (t : S) (n : ℕ) (ht : t ^ (n + 1) = 0)
    (hD : ∀ j : σ, D (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
      if i = j then 1 else 0)
    (hcoords : ∀ j : σ, g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
      f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) +
        if i = j then t else 0)
    (hred : ∀ x : R, g x - f x ∈ Ideal.span {t}) :
    g = NilpotentTaylorMap.Construction.nilpotentTaylorMap D f t (n + 1) ht := by
  symm
  apply TaylorCongruence.Construction.formallyUnramified_nilpotentTaylor_eq (P := MvPolynomial σ k) D f g t n ht
  · let α := IsScalarTower.toAlgHom k (MvPolynomial σ k) R
    have he : (NilpotentTaylorMap.Construction.nilpotentTaylorMap D f t (n + 1) ht).comp α = g.comp α := by
      apply MvPolynomial.algHom_ext
      intro j
      change NilpotentTaylorMap.Construction.nilpotentTaylorMap D f t (n + 1) ht
        (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) = _
      change _ = g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j))
      rw [hcoords j]
      by_cases hij : i = j
      · rw [ite_eq_left hij]
        exact NilpotentTaylorMap.Construction.nilpotentTaylorMap_coordinate D f t (n + 1) ht _
          (by simpa only [ite_eq_left hij] using hD j)
      · rw [ite_eq_right hij, add_zero]
        exact NilpotentTaylorMap.Construction.nilpotentTaylorMap_fixed D f t (n + 1) ht _
          (by simpa only [ite_eq_right hij] using hD j)
    exact fun p => AlgHom.congr_fun he p
  · exact hred

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TaylorShift.Construction
