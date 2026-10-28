import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Borel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Hecke

/-! # Borel Radial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BorelRadial.Iwasawa

noncomputable section

/-! Evaluate actual upper-triangular substitutions on the first coordinate
line. Its ball threshold is exactly the first Iwasawa valuation. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Hecke

variable (q : ℕ) [Fact q.Prime]

theorem borel_mulVec_first (b : Borel.Iwasawa.upperBorel q) (a : ℚ_[q]) :
    b.val.val.mulVec (Pi.single 0 a) = Pi.single 0 ((Borel.Iwasawa.diagonal q b 0 : ℚ_[q]) * a) := by
  funext i
  rw [Matrix.mulVec_single]
  by_cases hi : i = 0
  · subst i
    simp [Borel.Iwasawa.diagonal_apply]
  · have hz : b.val.val i 0 = 0 := b.property (by omega : (0 : Fin 3) < i)
    simp [hi, hz]

theorem borel_inverse_sphere_norm (b : Borel.Iwasawa.upperBorel q) (n : ℤ) :
    ‖(b.val⁻¹).val.mulVec (Radial.Hecke.spherePoint q n)‖ =
      Radial.Hecke.radius q (n - (Borel.Iwasawa.borelValuation q b).toAdd 0) := by
  change ‖(b⁻¹).val.val.mulVec (Pi.single 0 ((q : ℚ_[q]) ^ n))‖ = _
  rw [borel_mulVec_first, Pi.norm_single, norm_mul, map_inv]
  change ‖(Borel.Iwasawa.diagonal q b 0 : ℚ_[q])⁻¹‖ * ‖(q : ℚ_[q]) ^ n‖ = _
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation (Borel.Iwasawa.diagonal q b 0).ne_zero,
    Padic.norm_p_zpow, ← zpow_neg]
  rw [← zpow_add₀ (show (q : ℝ) ≠ 0 by exact_mod_cast (Fact.out : q.Prime).ne_zero)]
  congr 1
  change - -(b.val.val 0 0).valuation + -n = -(n - (b.val.val 0 0).valuation)
  omega

theorem borel_ball_sphere (b : Borel.Iwasawa.upperBorel q) (n : ℤ) :
    Radial.Hecke.matrixSubstitution q b.val (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0) (Radial.Hecke.spherePoint q n) =
      RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q ((Borel.Iwasawa.borelValuation q b).toAdd 0) (Radial.Hecke.spherePoint q n) := by
  change RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0
    ((↑((Matrix.SpecialLinearGroup.toGL b.val)⁻¹) : Matrix (Fin 3) (Fin 3) ℚ_[q]).mulVec
      (Radial.Hecke.spherePoint q n)) = _
  rw [← map_inv]
  change RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q 0 ((b.val⁻¹).val.mulVec (Radial.Hecke.spherePoint q n)) = _
  simp only [Radial.Hecke.ball_norm, borel_inverse_sphere_norm, Radial.Hecke.spherePoint_norm, Radial.Hecke.radius_le_iff,
    sub_nonneg]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BorelRadial.Iwasawa
