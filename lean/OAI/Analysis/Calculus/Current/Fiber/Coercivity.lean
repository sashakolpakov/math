import OAI.Analysis.Calculus.Current.Fiber.Height
import OAI.Analysis.PDE.Dirichlet.Coercivity

/-! A uniform lower bound for the spatial fiber Jacobian. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion Set Metric
open scoped Matrix Matrix.Norms.Elementwise

def admissibleRatios (d : ℕ) : Set (Fin d → ℂ) :=
  {W | (∑ i, ‖W i‖ ^ 2) ≤ (1 / 10 : ℝ) ^ 2}

theorem isCompact_admissibleRatios (d : ℕ) : IsCompact (admissibleRatios d) := by
  have hc : IsClosed (admissibleRatios d) := isClosed_le (by fun_prop) continuous_const
  apply (isCompact_closedBall (0 : Fin d → ℂ) 1).of_isClosed_subset hc
  intro W hW
  simp only [mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hi : ‖W i‖ ^ 2 ≤ ∑ j, ‖W j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖W j‖) (Finset.mem_univ i)
  change (∑ j, ‖W j‖ ^ 2) ≤ (1 / 10 : ℝ) ^ 2 at hW
  nlinarith [norm_nonneg (W i)]

theorem admissibleRatios_nonempty (d : ℕ) : (admissibleRatios d).Nonempty := by
  exact ⟨0, by simp [admissibleRatios]⟩

def modelFiberPoint {d : ℕ} (W : Fin d → ℂ) : Index d → ℂ
  | none => 1
  | some none => 0
  | some (some i) => W i

theorem ratio_modelFiberPoint {d : ℕ} (W : Fin d → ℂ) : ratio (modelFiberPoint W) = W := by
  funext i
  simp [ratio, modelFiberPoint]

def baseFiberJacobian {d : ℕ} (W : Fin d → ℂ) : Matrix (Option (Fin d)) (Index d) OAI.Analysis.Calculus.Quaternion.Q :=
  quaternionFiberJacobian 1 10 (modelFiberPoint W)

def fiberSpatialLift {d : ℕ} (v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q) : Index d → OAI.Analysis.Calculus.Quaternion.Q
  | none => v none
  | some none => v none
  | some (some i) => v (some i)

theorem fiberSpatialLift_injective (d : ℕ) : Function.Injective (fiberSpatialLift (d := d)) := by
  intro v w h
  funext i
  cases i with
  | none => exact congrFun h none
  | some i => exact congrFun h (some (some i))

theorem fiberSpatialLift_smul {d : ℕ} (r : ℝ) (v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q) :
    fiberSpatialLift (r • v) = r • fiberSpatialLift v := by
  funext b
  cases b with
  | none => rfl
  | some b => cases b <;> rfl

theorem continuous_fiberSpatialLift (d : ℕ) : Continuous (fiberSpatialLift (d := d)) := by
  apply continuous_pi
  intro b
  cases b with
  | none => exact continuous_apply none
  | some b => cases b <;> exact continuous_apply _

theorem continuous_baseFiberJacobian (d : ℕ) : Continuous (baseFiberJacobian (d := d)) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro b
  apply contDiff_complexK.continuous.comp
  cases i with
  | none =>
    cases b with
    | none => simp [fiberJacobian,
        phaseRow, ratio_modelFiberPoint]; fun_prop
    | some b => cases b <;>
        simp [fiberJacobian,
          phaseRow, ratio_modelFiberPoint] <;> fun_prop
  | some i =>
    cases b with
    | none => simp [fiberJacobian,
        ratioRow, ratio_modelFiberPoint, modelFiberPoint]; fun_prop
    | some b => cases b <;>
        simp [fiberJacobian,
          ratioRow, modelFiberPoint] <;> fun_prop

theorem baseFiberJacobian_spatial_injective {d : ℕ} (W : Fin d → ℂ)
    (hW : W ∈ admissibleRatios d) (v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q)
    (hv : baseFiberJacobian W *ᵥ fiberSpatialLift v = 0) : v = 0 := by
  have hD : fiberDenominator W ≠ 0 := fiberDenominator_ne_zero W (by
    change (∑ i, ‖W i‖ ^ 2) ≤ (1 / 10 : ℝ) ^ 2 at hW
    linarith)
  have hz := quaternionFiberJacobian_spatial_injective 1 10 (modelFiberPoint W)
    (fiberSpatialLift v) (by norm_num) (by norm_num) (by simp [modelFiberPoint])
    (by simpa [ratio_modelFiberPoint] using hD) rfl hv
  apply fiberSpatialLift_injective d
  have hzero : fiberSpatialLift (0 : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q) = 0 := by
    funext b
    cases b with
    | none => rfl
    | some b => cases b <;> rfl
  rw [hzero]
  exact hz

theorem baseFiberJacobian_uniform_lower (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ W ∈ admissibleRatios d, ∀ v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q,
      c * ‖v‖ ^ 2 ≤ ‖baseFiberJacobian W *ᵥ fiberSpatialLift v‖ ^ 2 := by
  have hs : (sphere (0 : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q) 1).Nonempty :=
    ⟨fun _ => 1, by simp []⟩
  apply OAI.Analysis.PDE.Dirichlet.uniform_positive_quadratic_lower
    (isCompact_admissibleRatios d) (admissibleRatios_nonempty d) hs
    (fun W v => ‖baseFiberJacobian W *ᵥ fiberSpatialLift v‖ ^ 2)
  · have hJ := continuous_baseFiberJacobian d
    have hv := continuous_fiberSpatialLift d
    apply Continuous.continuousOn
    fun_prop
  · intro W hW v hv
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    exact fun h => hv (baseFiberJacobian_spatial_injective W hW v h)
  · intro W hW r v
    simp [fiberSpatialLift_smul, Matrix.mulVec_smul, norm_smul, mul_pow]

end OAI.Analysis.Calculus.Current
