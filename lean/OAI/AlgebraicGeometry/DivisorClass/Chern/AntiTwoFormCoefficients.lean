import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormCoordinates
import OAI.AlgebraicTopology.DeRham.Comparison.DolbeaultProjection

/-! # Anti Two Form Coefficients -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.AntiTwoFormCoefficients

noncomputable section

/-! The original (0,2) character implies antiholomorphic dependence in each actual covector slot. -/

open _root_.ContinuousAlternatingMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicTopology.DeRham.Comparison.DolbeaultProjection

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def twoFormBilinear (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) : E →L[ℝ] E →L[ℝ] ℂ :=
  AntiOneFormCoordinates.oneFormLinearEquiv.symm.toContinuousLinearMap.comp a.curryLeft

theorem twoFormBilinear_apply (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (v w : E) :
    twoFormBilinear a v w = a ![v, w] := by
  change a (Matrix.vecCons v (fun _ : Fin 1 => w)) = a ![v, w]
  congr 1
  funext j
  fin_cases j <;> rfl

variable [NormedSpace ℂ E]

theorem antiTwoForm_J_both (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 2 a) (v w : E) :
    twoFormBilinear a (Complex.I • v) (Complex.I • w) = -twoFormBilinear a v w := by
  have h := ha AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit ![v, w]
  simp only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, one_mul, AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe, Complex.star_def,
    Complex.conj_I, neg_sq, Complex.I_sq, neg_one_mul] at h
  rw [twoFormBilinear_apply, twoFormBilinear_apply]
  have ht : (fun i : Fin 2 => Complex.I • ![v, w] i) = ![Complex.I • v, Complex.I • w] := by
    funext j
    fin_cases j <;> rfl
  rw [ht] at h
  exact h

theorem antiTwoForm_J_interchange (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 2 a) (v w : E) :
    twoFormBilinear a (Complex.I • v) w = twoFormBilinear a v (Complex.I • w) := by
  have h := antiTwoForm_J_both a ha v (Complex.I • w)
  rw [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at h
  exact neg_inj.mp h

theorem antiTwoForm_J_left (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 2 a) (v w : E) :
    twoFormBilinear a (Complex.I • v) w = -Complex.I * twoFormBilinear a v w := by
  let c : ℂˣ := Units.mk0 (1 + Complex.I) (by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr)
  have h := ha c ![v, w]
  have hc : Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 2 c = -2 * Complex.I := by
    simp only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, one_mul, c, Units.val_mk0,
      star_add, star_one, Complex.star_def, Complex.conj_I]
    calc
      _ = 1 - 2 * Complex.I + Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [hc] at h
  have ht : (fun i : Fin 2 => (c : ℂ) • ![v, w] i) = ![(1 + Complex.I) • v, (1 + Complex.I) • w] := by
    funext j
    fin_cases j <;> rfl
  rw [ht, ← twoFormBilinear_apply, ← twoFormBilinear_apply] at h
  rw [add_smul, one_smul, add_smul, one_smul, (twoFormBilinear a).map_add] at h
  simp only [_root_.add_apply, map_add] at h
  rw [antiTwoForm_J_both a ha, ← antiTwoForm_J_interchange a ha] at h
  linear_combination (1 / 2 : ℂ) * h

theorem antiTwoForm_J_right (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 2 a) (v w : E) :
    twoFormBilinear a v (Complex.I • w) = -Complex.I * twoFormBilinear a v w :=
  (antiTwoForm_J_interchange a ha v w).symm.trans (antiTwoForm_J_left a ha v w)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.AntiTwoFormCoefficients
