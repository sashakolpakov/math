import OAI.NumberTheory.Quaternion.Arithmetic.PolynomialAdditiveCurves
import OAI.NumberTheory.Quaternion.Arithmetic.LocalAdeles

/-! # Integral Polynomial Curves -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.IntegralPolynomialCurves

noncomputable section

/-! A polynomial additive curve preserves integral local points at all
but finitely many places, uniformly in its integral parameter. -/

open scoped Classical
open Filter

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem eventually_integral_polynomial (p : Polynomial F) :
    ∀ᶠ v : LocalAdeles.Place F in cofinite, ∀ t ∈ LocalAdeles.localIntegerRing v,
      p.eval₂ (LocalAdeles.localEmbedding v) t ∈ LocalAdeles.localIntegerRing v := by
  have hc : ∀ᶠ v : LocalAdeles.Place F in cofinite, ∀ k ∈ p.support,
      LocalAdeles.localEmbedding v (p.coeff k) ∈ LocalAdeles.localIntegerRing v :=
    (p.support.eventually_all).mpr (fun k _ => LocalAdeles.eventually_integral_scalar (p.coeff k))
  filter_upwards [hc] with v hv
  intro t ht
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  exact (LocalAdeles.localIntegerRing v).sum_mem fun k hk =>
    (LocalAdeles.localIntegerRing v).mul_mem (hv k hk) ((LocalAdeles.localIntegerRing v).pow_mem ht k)

theorem polynomialAdditiveCurve_eventually_integral (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (u : PolynomialAdditiveCurves.PolynomialAdditiveCurve G) :
    ∀ᶠ v : LocalAdeles.Place F in cofinite, Set.MapsTo
      (fun t : LocalAdeles.Completion v => u.hom (LocalAdeles.Completion v) (LocalAdeles.localEmbedding v) (Multiplicative.ofAdd t))
      (LocalAdeles.localIntegerRing v) (LocalAdeles.integralLocalSubgroup G v) := by
  have hc : ∀ᶠ v : LocalAdeles.Place F in cofinite, ∀ i j : Fin n, ∀ t ∈ LocalAdeles.localIntegerRing v,
      (u.coordinates i j).eval₂ (LocalAdeles.localEmbedding v) t ∈ LocalAdeles.localIntegerRing v :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      eventually_integral_polynomial (u.coordinates i j)
  filter_upwards [hc] with v hv
  intro t ht
  have hi : (u.hom (LocalAdeles.Completion v) (LocalAdeles.localEmbedding v) (Multiplicative.ofAdd t))⁻¹ =
      u.hom (LocalAdeles.Completion v) (LocalAdeles.localEmbedding v) (Multiplicative.ofAdd (-t)) :=
    (map_inv (u.hom (LocalAdeles.Completion v) (LocalAdeles.localEmbedding v)) (Multiplicative.ofAdd t)).symm
  constructor
  · intro i j
    change PolynomialGaloisNorm.matrixPointsHom G (LocalAdeles.localEmbedding v)
      (u.hom (LocalAdeles.Completion v) (LocalAdeles.localEmbedding v) (Multiplicative.ofAdd t)) i j ∈ LocalAdeles.localIntegerRing v
    rw [u.coordinate_eq]
    exact hv i j t ht
  · intro i j
    rw [hi]
    change PolynomialGaloisNorm.matrixPointsHom G (LocalAdeles.localEmbedding v)
      (u.hom (LocalAdeles.Completion v) (LocalAdeles.localEmbedding v) (Multiplicative.ofAdd (-t))) i j ∈ LocalAdeles.localIntegerRing v
    rw [u.coordinate_eq]
    exact hv i j (-t) ((LocalAdeles.localIntegerRing v).neg_mem ht)

end

end OAI.NumberTheory.Quaternion.Arithmetic.IntegralPolynomialCurves
