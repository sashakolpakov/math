import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Complex.Basic

/-! # Monic Root -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.MonicRoot.Constructions.MonicRootBound

noncomputable section

/-! # RiemannProjectivity: a coefficient bound for roots of a monic polynomial -/

open _root_.Polynomial
open scoped BigOperators

theorem norm_root_le_sum_coeff {p : Polynomial ℂ} (hp : p.Monic) {d : ℕ}
    (hdeg : p.natDegree ≤ d) {z : ℂ} (hz : p.eval z = 0) :
    ‖z‖ ≤ (∑ j ∈ Finset.range d, ‖p.coeff j‖) + 1 := by
  have hroot : p.IsRoot z := hz
  have hcb : p.cauchyBound ≤ (∑ j ∈ Finset.range d, ‖p.coeff j‖₊) + 1 := by
    rw [Polynomial.cauchyBound, hp.leadingCoeff, nnnorm_one, div_one]
    refine add_le_add ?_ le_rfl
    apply Finset.sup_le
    intro j hj
    exact Finset.single_le_sum (f := fun k => ‖p.coeff k‖₊) (fun _ _ => zero_le)
      (Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hdeg))
  have h := (hroot.norm_lt_cauchyBound hp.ne_zero).le.trans hcb
  have hreal := NNReal.coe_le_coe.mpr h
  simpa only [NNReal.coe_add, NNReal.coe_sum, NNReal.coe_one, coe_nnnorm] using hreal

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.MonicRoot.Constructions.MonicRootBound
