import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallPlaneGroups

/-! # Split Plane Elimination -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SplitPlaneElimination.CM

noncomputable section

/-! Explicit elimination in a split unitary plane, retaining its
normalization and its action on the original complex coordinates. -/

open scoped ComplexConjugate
open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

def splitPlaneEliminator (x z : ℂ) (r : ℝ) (hr : 0 < r)
    (hn : Complex.normSq z - Complex.normSq x = r ^ 2) : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU SplitUnitaryPlane.CM.splitPlaneForm :=
  BallPlaneGroups.CM.splitPlaneElement (z / (r : ℂ)) (-x / (r : ℂ)) (by
    simp only [Complex.normSq_div, Complex.normSq_neg, Complex.normSq_ofReal,
      ← sub_div, hn]
    simpa only [pow_two] using div_self (pow_ne_zero 2 (ne_of_gt hr)))

theorem split_plane_eliminator_action (x z : ℂ) (r : ℝ) (hr : 0 < r)
    (hn : Complex.normSq z - Complex.normSq x = r ^ 2) :
    (splitPlaneEliminator x z r hr hn).val.val.mulVec ![x, z] = ![0, (r : ℂ)] := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hc : z * conj z - x * conj x = (r : ℂ) ^ 2 := by
    simpa only [Complex.mul_conj, Complex.ofReal_sub, Complex.ofReal_pow] using congrArg Complex.ofReal hn
  change (!![z / (r : ℂ), -x / (r : ℂ);
    conj (-x / (r : ℂ)), conj (z / (r : ℂ))] : Matrix (Fin 2) (Fin 2) ℂ).mulVec ![x, z] = _
  funext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    change z / (r : ℂ) * x + (-x / (r : ℂ)) * z = 0
    ring
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    change conj (-x / (r : ℂ)) * x + conj (z / (r : ℂ)) * z = r
    simp only [map_div₀, map_neg, Complex.conj_ofReal]
    field_simp
    linear_combination hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SplitPlaneElimination.CM
