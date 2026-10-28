import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Borel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity

/-! # Satake Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeParameters.Iwasawa

noncomputable section

/-! The normalized radial torus parameter is the explicit triple
(e, sqrt(q), sqrt(q) inverse). The determinant-one lattice makes the
modulus-weighted monomial equal the radial dilation monomial. -/

open scoped Classical

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity

variable (q : ℕ) [Fact q.Prime]

def sqrtUnit : ℂˣ := RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.residueSqrtUnit q (Fact.out : q.Prime).pos

theorem normalization_eq_sqrt_cube : Radial.Cyclicity.normalization q = (sqrtUnit q : ℂ) ^ 3 := by
  change (Real.rpow (q : ℝ) (3 / 2 : ℝ) : ℂ) = (Real.sqrt (q : ℝ) : ℂ) ^ 3
  rw [← Complex.ofReal_pow]
  apply congrArg Complex.ofReal
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
  congr 1
  norm_num

def radialTorusPoint (e : ℂˣ) : Fin 3 → ℂˣ := ![e, sqrtUnit q, (sqrtUnit q)⁻¹]

def torusCharacter (t : Fin 3 → ℂˣ) : Multiplicative (Fin 3 → ℤ) →* ℂˣ where
  toFun ell := ∏ i, t i ^ ell.toAdd i
  map_one' := by simp
  map_mul' a b := by
    change (∏ i, t i ^ (a.toAdd i + b.toAdd i)) = _
    simp only [zpow_add, Finset.prod_mul_distrib]

theorem radialTorusPoint_weight (e : ℂˣ) (ell : Fin 3 → ℤ)
    (hell : ∑ i, ell i = 0) :
    RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.modulusWeight q (Fact.out : q.Prime).pos RepresentationTheory.Satake.GL3GL.Core.twoRho
        (Multiplicative.ofAdd ell) *
      torusCharacter (radialTorusPoint q e) (Multiplicative.ofAdd ell) =
        (e / (sqrtUnit q) ^ 3) ^ ell 0 := by
  have hsum : ell 0 + ell 1 + ell 2 = 0 := by
    simpa only [Fin.sum_univ_three] using hell
  change sqrtUnit q ^ (-(2 * (ell 0 - ell 2))) *
    (∏ i, radialTorusPoint q e i ^ ell i) = _
  rw [Fin.prod_univ_three]
  change sqrtUnit q ^ (-(2 * (ell 0 - ell 2))) *
    (e ^ ell 0 * sqrtUnit q ^ ell 1 * ((sqrtUnit q)⁻¹) ^ ell 2) = _
  rw [inv_zpow, div_zpow, ← zpow_natCast (sqrtUnit q) 3, ← zpow_mul]
  rw [div_eq_mul_inv, ← zpow_neg, ← zpow_neg]
  calc
    _ = e ^ ell 0 * (sqrtUnit q ^ (-(2 * (ell 0 - ell 2))) *
        sqrtUnit q ^ ell 1 * sqrtUnit q ^ (-ell 2)) := by
      simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = e ^ ell 0 * sqrtUnit q ^ (-(2 * (ell 0 - ell 2)) + ell 1 + -ell 2) := by
      rw [zpow_add, zpow_add]
    _ = _ := by congr 2; omega

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeParameters.Iwasawa
