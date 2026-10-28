import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftScale
import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftBoundary
import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftContinuous

noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance assemblyDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance assemblyDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance assemblyBilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance assemblyBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance assemblyTrilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance assemblyTrilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Quantitative data supplied by smoothing a Hölder boundary value at the normal scale. -/
structure BoundaryLiftRegularization (ℓ : E →L[ℝ] ℝ) (α : ℝ) where
  s : E → ℝ
  b : E → ℝ
  D : E → E →L[ℝ] ℝ
  DD : E → E →L[ℝ] E →L[ℝ] ℝ
  DDD : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ
  M : ℝ
  H : ℝ
  C0 : ℝ
  C1 : ℝ
  C2 : ℝ
  C3 : ℝ
  nonneg_M : 0 ≤ M
  nonneg_H : 0 ≤ H
  nonneg_C0 : 0 ≤ C0
  nonneg_C1 : 0 ≤ C1
  nonneg_C2 : 0 ≤ C2
  nonneg_C3 : 0 ≤ C3
  bounded : ∀ x, |s x| ≤ M
  holder : ∀ x y, |b x - b y| ≤ H * ‖x - y‖ ^ α
  error : ∀ x, |s x - b x| ≤ C0 * |ℓ x| ^ α
  deriv_s : ∀ x, ℓ x ≠ 0 → HasFDerivAt s (D x) x
  deriv_D : ∀ x, ℓ x ≠ 0 → HasFDerivAt D (DD x) x
  deriv_DD : ∀ x, ℓ x ≠ 0 → HasFDerivAt DD (DDD x) x
  bound_D : ∀ x, ℓ x ≠ 0 → ‖D x‖ ≤ C1 * |ℓ x| ^ (α - 1)
  bound_DD : ∀ x, ℓ x ≠ 0 → ‖DD x‖ ≤ C2 * |ℓ x| ^ (α - 2)
  bound_DDD : ∀ x, ℓ x ≠ 0 → ‖DDD x‖ ≤ C3 * |ℓ x| ^ (α - 3)

namespace BoundaryLiftRegularization

variable {ℓ : E →L[ℝ] ℝ} {α : ℝ}

def value (a : BoundaryLiftRegularization ℓ α) (x : E) : ℝ := (ℓ x) ^ 2 / 2 * a.s x
def first (a : BoundaryLiftRegularization ℓ α) := liftFirstJet ℓ a.s a.D
def second (a : BoundaryLiftRegularization ℓ α) := liftSecondJet ℓ a.s a.D a.DD
def holderConstant (a : BoundaryLiftRegularization ℓ α) : ℝ :=
  (3 * a.C1 + 3 * a.C2 + a.C3 / 2) +
    (a.C0 + 2 * a.C1 + a.C2 / 2) * ((2 : ℝ) ^ α + (3 : ℝ) ^ α) + a.H

theorem hasFDerivAt_value (a : BoundaryLiftRegularization ℓ α) (hℓ : ‖ℓ‖ ≤ 1)
    (x : E) : HasFDerivAt a.value (a.first x) x := by
  by_cases hx : ℓ x = 0
  · have h := hasFDerivAt_quadraticLift_boundary ℓ hℓ a.s a.nonneg_M a.bounded hx
    change HasFDerivAt (fun y ↦ (ℓ y) ^ 2 / 2 * a.s y) (liftFirstJet ℓ a.s a.D x) x
    rw [liftFirstJet_boundary ℓ a.s a.D hx]
    exact h
  · exact hasFDerivAt_quadraticLift ℓ a.s a.D x (a.deriv_s x hx)

theorem first_error (a : BoundaryLiftRegularization ℓ α) (hℓ : ‖ℓ‖ ≤ 1)
    (hα : 0 < α) (x : E) :
    ‖a.first x - ℓ x • (a.b x • ℓ)‖ ≤ (a.C0 + a.C1 / 2) * |ℓ x| ^ (1 + α) := by
  by_cases hx : ℓ x = 0
  · simp [BoundaryLiftRegularization.first, hx,
      Real.zero_rpow (by linarith : 1 + α ≠ 0)]
  · exact liftFirstJet_scale_error ℓ hℓ a.s a.D x (a.b x) hx
      (a.error x) (a.bound_D x hx)

theorem hasFDerivAt_first (a : BoundaryLiftRegularization ℓ α) (hℓ : ‖ℓ‖ ≤ 1)
    (hα : 0 < α) (x : E) : HasFDerivAt a.first (a.second x) x := by
  by_cases hx : ℓ x = 0
  · have hb := eq_boundary_of_scale_error ℓ a.s a.b hα a.error hx
    have hd := hasFDerivAt_boundary_firstJet ℓ hℓ a.first (fun y ↦ a.b y • ℓ)
      hα (add_nonneg a.nonneg_C0 (div_nonneg a.nonneg_C1 (by norm_num)))
      a.nonneg_H (holder_smul_fixed a.b a.holder ℓ hℓ) (a.first_error hℓ hα) hx
    convert! hd using 1
    ext v w
    simp [BoundaryLiftRegularization.second, liftSecondJet_boundary ℓ a.s a.D a.DD hx, hb,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring
  · exact hasFDerivAt_liftFirstJet ℓ a.s a.D a.DD x (a.deriv_s x hx) (a.deriv_D x hx)

theorem second_error (a : BoundaryLiftRegularization ℓ α) (hℓ : ‖ℓ‖ ≤ 1)
    (hα : 0 < α) (x : E) :
    ‖a.second x - a.b x • ℓ.smulRight ℓ‖ ≤
      (a.C0 + 2 * a.C1 + a.C2 / 2) * |ℓ x| ^ α := by
  by_cases hx : ℓ x = 0
  · have hb := eq_boundary_of_scale_error ℓ a.s a.b hα a.error hx
    simp [BoundaryLiftRegularization.second, hb, hx,
      Real.zero_rpow hα.ne']
  · exact liftSecondJet_scale_error ℓ hℓ a.s a.D a.DD x (a.b x) hx
      (a.error x) (a.bound_D x hx) (a.bound_DD x hx)

theorem second_holder (a : BoundaryLiftRegularization ℓ α) (hℓ : ‖ℓ‖ ≤ 1)
    (hα : 0 < α) (hαone : α < 1) (x y : E) :
    ‖a.second x - a.second y‖ ≤ a.holderConstant * ‖x - y‖ ^ α := by
  apply holder_of_boundary_jet_and_derivative ℓ hℓ a.second
    (fun z ↦ a.b z • ℓ.smulRight ℓ) hα hαone
    (add_nonneg (add_nonneg a.nonneg_C0 (mul_nonneg (by norm_num) a.nonneg_C1))
      (div_nonneg a.nonneg_C2 (by norm_num))) a.nonneg_H
    (add_nonneg (add_nonneg (mul_nonneg (by norm_num) a.nonneg_C1)
      (mul_nonneg (by norm_num) a.nonneg_C2)) (div_nonneg a.nonneg_C3 (by norm_num)))
    (a.second_error hℓ hα)
    (holder_smul_fixed a.b a.holder (ℓ.smulRight ℓ) (norm_normalTensor_le ℓ hℓ))
  · intro z hz
    exact differentiableAt_liftSecondJet ℓ a.s a.D a.DD a.DDD z
      (a.deriv_s z hz) (a.deriv_D z hz) (a.deriv_DD z hz)
  · intro z hz
    exact liftSecondJet_derivative_scale_bound ℓ hℓ a.s a.D a.DD a.DDD z hz
      (a.deriv_s z hz) (a.deriv_D z hz) (a.deriv_DD z hz)
      (a.bound_D z hz) (a.bound_DD z hz) (a.bound_DDD z hz)

theorem contDiff_value (a : BoundaryLiftRegularization ℓ α) (hℓ : ‖ℓ‖ ≤ 1)
    (hα : 0 < α) (hαone : α < 1) : ContDiff ℝ 2 a.value := by
  exact contDiff_two_of_derivative_fields a.value a.first a.second
    (a.hasFDerivAt_value hℓ) (a.hasFDerivAt_first hℓ hα)
    (continuous_of_real_holder_bound a.second hα (a.second_holder hℓ hα hαone))

theorem fderiv_value (a : BoundaryLiftRegularization ℓ α) (hℓ : ‖ℓ‖ ≤ 1) :
    fderiv ℝ a.value = a.first := funext (fun x ↦ (a.hasFDerivAt_value hℓ x).fderiv)

theorem fderiv_fderiv_value (a : BoundaryLiftRegularization ℓ α) (hℓ : ‖ℓ‖ ≤ 1)
    (hα : 0 < α) : fderiv ℝ (fderiv ℝ a.value) = a.second := by
  rw [a.fderiv_value hℓ]
  exact funext (fun x ↦ (a.hasFDerivAt_first hℓ hα x).fderiv)

end BoundaryLiftRegularization
end OAI.Analysis.PDE.Schauder
