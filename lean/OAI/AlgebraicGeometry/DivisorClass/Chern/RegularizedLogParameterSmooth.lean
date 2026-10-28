import OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogWeight
import OAI.AlgebraicGeometry.DivisorClass.Chern.ParametricScalarCurvature

/-! # Regularized Log Parameter Smooth -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogParameterSmooth

noncomputable section

/-! The actual logarithmic cutoff curvature is continuous down to parameter zero on every compact coordinate set avoiding its center. -/

open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def regularizedLogSmoothDomain (x : E) : Set (ℝ × E) := {p | 0 < p.1 + ‖p.2 - x‖ ^ 2}

omit [InnerProductSpace ℝ E] in
theorem regularizedLogSmoothDomain_open (x : E) : IsOpen (regularizedLogSmoothDomain x) :=
  isOpen_lt continuous_const (continuous_fst.add ((continuous_snd.sub continuous_const).norm.pow 2))

theorem regularizedLogCutoff_parameter_smooth (x : E) (m : ℕ) (η : E → ℝ) (hη : ContDiff ℝ ∞ η) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => η p.2 * RegularizedLogWeight.regularizedNegativeLog x m p.1 p.2) (regularizedLogSmoothDomain x) := by
  have hq : ContDiff ℝ ∞ (fun p : ℝ × E => p.1 + ‖p.2 - x‖ ^ 2) :=
    contDiff_fst.add ((contDiff_snd.sub contDiff_const).norm_sq (𝕜 := ℝ))
  exact (hη.comp contDiff_snd).contDiffOn.mul
    (contDiffOn_const.mul (hq.contDiffOn.log (fun _ hp => ne_of_gt hp)))

omit [InnerProductSpace ℝ E] in
theorem regularizedLogSmoothDomain_contains (x : E) {K : Set E} (hx : x ∉ K) :
    Icc (0 : ℝ) 1 ×ˢ K ⊆ regularizedLogSmoothDomain x := by
  intro p hp
  have hne : p.2 - x ≠ 0 := fun heq => hx ((sub_eq_zero.mp heq) ▸ hp.2)
  exact add_pos_of_nonneg_of_pos hp.1.1 (sq_pos_of_pos (norm_pos_iff.mpr hne))

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem regularizedLogCutoff_curvature_continuous (x : E) (m : ℕ) (η : E → ℝ) (hη : ContDiff ℝ ∞ η)
    {K : Set E} (hx : x ∉ K) :
    ContinuousOn (fun p : ℝ × E => extDeriv
      (fun y => RealScalarOperator.realScalarChernOperator E (fderiv ℝ (η * RegularizedLogWeight.regularizedNegativeLog x m p.1) y)) p.2)
      (Icc (0 : ℝ) 1 ×ˢ K) :=
  (ParametricScalarCurvature.parametricScalarChernCurvature_smoothOn _ (regularizedLogSmoothDomain_open x)
    (regularizedLogCutoff_parameter_smooth x m η hη)).continuousOn.mono (regularizedLogSmoothDomain_contains x hx)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogParameterSmooth
