import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Transcendental Power Independence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranscendentalPowerIndependence

noncomputable section

/-! Powers of a transcendental element are linearly independent, and any finite section space realizing their initial segment has the corresponding dimension lower bound. -/

universe u v w

variable {K : Type u} [Field K] {R : Type v} [CommRing R] [Algebra K R]

theorem transcendental_powers_linearIndependent (x : R) (hx : Transcendental K x) :
    LinearIndependent K (fun n : ℕ => x ^ n) := by
  have h := (Polynomial.basisMonomials K).linearIndependent.map'
    (Polynomial.aeval x).toLinearMap (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hx))
  simpa only [Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow, Function.comp_def,
    AlgHom.toLinearMap_apply, map_pow, Polynomial.aeval_X] using h

theorem transcendental_initialPowers_linearIndependent (x : R) (hx : Transcendental K x) (d : ℕ) :
    LinearIndependent K (fun i : Fin (d + 1) => x ^ (i : ℕ)) :=
  (transcendental_powers_linearIndependent x hx).comp _ Fin.val_injective

theorem transcendental_powerValues_dimension_bound
    {V : Type w} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (φ : V →ₗ[K] R) (x : R) (hx : Transcendental K x) (d : ℕ)
    (v : Fin (d + 1) → V) (hv : ∀ i, φ (v i) = x ^ (i : ℕ)) :
    d + 1 ≤ Module.finrank K V := by
  have h : LinearIndependent K (fun i => φ (v i)) := by
    simpa only [hv] using transcendental_initialPowers_linearIndependent x hx d
  simpa only [Fintype.card_fin] using (LinearIndependent.of_comp φ h).fintype_card_le_finrank

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranscendentalPowerIndependence
