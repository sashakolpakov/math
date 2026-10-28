import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeParameters

/-! # Dual Satake Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualSatakeParameters.Iwasawa

noncomputable section

/-! The inverse-transpose radial convention has the explicit normalized
triple (sqrt(q), sqrt(q) inverse, e inverse). -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]

def dualRadialTorusPoint (e : ℂˣ) : Fin 3 → ℂˣ := ![SatakeParameters.Iwasawa.sqrtUnit q, (SatakeParameters.Iwasawa.sqrtUnit q)⁻¹, e⁻¹]

theorem dualRadialTorusPoint_weight (e : ℂˣ) (ell : Fin 3 → ℤ)
    (hell : ∑ i, ell i = 0) :
    RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.modulusWeight q (Fact.out : q.Prime).pos RepresentationTheory.Satake.GL3GL.Core.twoRho
        (Multiplicative.ofAdd ell) *
      SatakeParameters.Iwasawa.torusCharacter (dualRadialTorusPoint q e) (Multiplicative.ofAdd ell) =
        (e / (SatakeParameters.Iwasawa.sqrtUnit q) ^ 3) ^ (-ell 2) := by
  have hsum : ell 0 + ell 1 + ell 2 = 0 := by
    simpa only [Fin.sum_univ_three] using hell
  change SatakeParameters.Iwasawa.sqrtUnit q ^ (-(2 * (ell 0 - ell 2))) *
    (∏ i, dualRadialTorusPoint q e i ^ ell i) = _
  rw [Fin.prod_univ_three]
  change SatakeParameters.Iwasawa.sqrtUnit q ^ (-(2 * (ell 0 - ell 2))) *
    (SatakeParameters.Iwasawa.sqrtUnit q ^ ell 0 * ((SatakeParameters.Iwasawa.sqrtUnit q)⁻¹) ^ ell 1 * (e⁻¹) ^ ell 2) = _
  rw [inv_zpow, inv_zpow, div_zpow, ← zpow_natCast (SatakeParameters.Iwasawa.sqrtUnit q) 3, ← zpow_mul]
  rw [div_eq_mul_inv, ← zpow_neg, ← zpow_neg, ← zpow_neg]
  calc
    _ = e ^ (-ell 2) * (SatakeParameters.Iwasawa.sqrtUnit q ^ (-(2 * (ell 0 - ell 2))) *
        SatakeParameters.Iwasawa.sqrtUnit q ^ ell 0 * SatakeParameters.Iwasawa.sqrtUnit q ^ (-ell 1)) := by
      simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = e ^ (-ell 2) * SatakeParameters.Iwasawa.sqrtUnit q ^ (-(2 * (ell 0 - ell 2)) + ell 0 + -ell 1) := by
      rw [zpow_add, zpow_add]
    _ = _ := by congr 2; omega

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualSatakeParameters.Iwasawa
