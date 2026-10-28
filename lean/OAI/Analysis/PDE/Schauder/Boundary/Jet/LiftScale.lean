import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftThird
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance scaleDualNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance scaleDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance scaleBilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance scaleBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance scaleTrilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance scaleTrilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem height_rpow_cancel_one {t : ℝ} (ht : 0 < t) (a : ℝ) :
    t * t ^ (a - 1) = t ^ a := by
  rw [Real.rpow_sub_one ht.ne']
  field_simp

theorem height_rpow_cancel_two {t : ℝ} (ht : 0 < t) (a : ℝ) :
    t ^ 2 * t ^ (a - 2) = t ^ a := by
  calc
    _ = t ^ (2 : ℝ) * t ^ (a - 2) := by rw [Real.rpow_two]
    _ = t ^ ((2 : ℝ) + (a - 2)) := (Real.rpow_add ht _ _).symm
    _ = t ^ a := by congr 1; ring

theorem liftFirstJet_scale_error (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1)
    (s : E → ℝ) (D : E → E →L[ℝ] ℝ) (x : E) (b : ℝ)
    {α C0 C1 : ℝ} (ht : ℓ x ≠ 0)
    (h0 : |s x - b| ≤ C0 * |ℓ x| ^ α)
    (h1 : ‖D x‖ ≤ C1 * |ℓ x| ^ (α - 1)) :
    ‖liftFirstJet ℓ s D x - ℓ x • (b • ℓ)‖ ≤
      (C0 + C1 / 2) * |ℓ x| ^ (1 + α) := by
  have htpos : 0 < |ℓ x| := abs_pos.mpr ht
  have ha := mul_le_mul_of_nonneg_left h0 (abs_nonneg (ℓ x))
  have hb := mul_le_mul_of_nonneg_left h1 (div_nonneg (sq_nonneg (ℓ x)) (by norm_num : (0 : ℝ) ≤ 2))
  have hp0 : |ℓ x| * |ℓ x| ^ α = |ℓ x| ^ (1 + α) := by
    rw [Real.rpow_add htpos, Real.rpow_one]
  have hp1 : (ℓ x) ^ 2 * |ℓ x| ^ (α - 1) = |ℓ x| ^ (1 + α) := by
    rw [← sq_abs (ℓ x)]
    convert height_rpow_cancel_two htpos (1 + α) using 1 ; congr 1 ; ring_nf
  have hraw := norm_liftFirstJet_sub_le ℓ hℓ s D x b
  calc
    _ ≤ |ℓ x| * (C0 * |ℓ x| ^ α) + (ℓ x) ^ 2 / 2 * (C1 * |ℓ x| ^ (α - 1)) :=
      hraw.trans (add_le_add ha hb)
    _ = _ := by
      calc
        _ = C0 * (|ℓ x| * |ℓ x| ^ α) + C1 / 2 * ((ℓ x) ^ 2 * |ℓ x| ^ (α - 1)) := by ring
        _ = _ := by rw [hp0, hp1]; ring

theorem liftSecondJet_scale_error (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1)
    (s : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (DD : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) (b : ℝ)
    {α C0 C1 C2 : ℝ} (ht : ℓ x ≠ 0)
    (h0 : |s x - b| ≤ C0 * |ℓ x| ^ α)
    (h1 : ‖D x‖ ≤ C1 * |ℓ x| ^ (α - 1))
    (h2 : ‖DD x‖ ≤ C2 * |ℓ x| ^ (α - 2)) :
    ‖liftSecondJet ℓ s D DD x - b • ℓ.smulRight ℓ‖ ≤
      (C0 + 2 * C1 + C2 / 2) * |ℓ x| ^ α := by
  have htpos : 0 < |ℓ x| := abs_pos.mpr ht
  have h1' := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg (ℓ x)))
  have h2' := mul_le_mul_of_nonneg_left h2 (div_nonneg (sq_nonneg (ℓ x)) (by norm_num : (0 : ℝ) ≤ 2))
  have hp1 := height_rpow_cancel_one htpos α
  have hp2 : (ℓ x) ^ 2 * |ℓ x| ^ (α - 2) = |ℓ x| ^ α := by
    rw [← sq_abs (ℓ x)]
    exact height_rpow_cancel_two htpos α
  calc
    _ ≤ C0 * |ℓ x| ^ α + 2 * |ℓ x| * (C1 * |ℓ x| ^ (α - 1)) +
        (ℓ x) ^ 2 / 2 * (C2 * |ℓ x| ^ (α - 2)) :=
      (norm_liftSecondJet_sub_le ℓ hℓ s D DD x b).trans (add_le_add (add_le_add h0 h1') h2')
    _ = _ := by
      calc
        _ = C0 * |ℓ x| ^ α + 2 * C1 * (|ℓ x| * |ℓ x| ^ (α - 1)) +
            C2 / 2 * ((ℓ x) ^ 2 * |ℓ x| ^ (α - 2)) := by ring
        _ = _ := by rw [hp1, hp2]; ring

theorem liftSecondJet_derivative_scale_bound (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1)
    (s : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    (DDD : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (x : E) {α C1 C2 C3 : ℝ} (ht : ℓ x ≠ 0)
    (hs : HasFDerivAt s (D x) x) (hD : HasFDerivAt D (DD x) x)
    (hDD : HasFDerivAt DD (DDD x) x)
    (h1 : ‖D x‖ ≤ C1 * |ℓ x| ^ (α - 1))
    (h2 : ‖DD x‖ ≤ C2 * |ℓ x| ^ (α - 2))
    (h3 : ‖DDD x‖ ≤ C3 * |ℓ x| ^ (α - 3)) :
    ‖fderiv ℝ (liftSecondJet ℓ s D DD) x‖ ≤
      (3 * C1 + 3 * C2 + C3 / 2) * |ℓ x| ^ (α - 1) := by
  have htpos : 0 < |ℓ x| := abs_pos.mpr ht
  have ha := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)
  have hb := mul_le_mul_of_nonneg_left h2
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (abs_nonneg (ℓ x)))
  have hc := mul_le_mul_of_nonneg_left h3
    (div_nonneg (sq_nonneg (ℓ x)) (by norm_num : (0 : ℝ) ≤ 2))
  have hp1 : |ℓ x| * |ℓ x| ^ (α - 2) = |ℓ x| ^ (α - 1) := by
    convert height_rpow_cancel_one htpos (α - 1) using 1 ; congr 1 ; ring_nf
  have hp2 : (ℓ x) ^ 2 * |ℓ x| ^ (α - 3) = |ℓ x| ^ (α - 1) := by
    rw [← sq_abs (ℓ x)]
    convert height_rpow_cancel_two htpos (α - 1) using 1 ; congr 1 ; ring_nf
  calc
    _ ≤ 3 * (C1 * |ℓ x| ^ (α - 1)) +
        3 * |ℓ x| * (C2 * |ℓ x| ^ (α - 2)) +
        (ℓ x) ^ 2 / 2 * (C3 * |ℓ x| ^ (α - 3)) :=
      (norm_fderiv_liftSecondJet_le ℓ hℓ s D DD DDD x hs hD hDD).trans
        (add_le_add (add_le_add ha hb) hc)
    _ = _ := by
      calc
        _ = 3 * C1 * |ℓ x| ^ (α - 1) +
            3 * C2 * (|ℓ x| * |ℓ x| ^ (α - 2)) +
            C3 / 2 * ((ℓ x) ^ 2 * |ℓ x| ^ (α - 3)) := by ring
        _ = _ := by rw [hp1, hp2]; ring

end OAI.Analysis.PDE.Schauder
