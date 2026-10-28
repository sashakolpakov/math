import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftCalculus
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance liftDualNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance liftDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance liftBilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance liftBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def crossJetMap (ℓ : E →L[ℝ] ℝ) :
    (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).flip ℓ +
    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ) ℓ

@[simp] theorem crossJetMap_apply (ℓ D : E →L[ℝ] ℝ) :
    crossJetMap ℓ D = D.smulRight ℓ + ℓ.smulRight D := rfl

theorem norm_crossJetMap_apply_le (ℓ D : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) :
    ‖crossJetMap ℓ D‖ ≤ 2 * ‖D‖ := by
  rw [crossJetMap_apply]
  have ht := norm_add_le (D.smulRight ℓ) (ℓ.smulRight D)
  rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_smulRight_apply] at ht
  nlinarith [mul_le_mul_of_nonneg_left hℓ (norm_nonneg D)]

theorem norm_crossJetMap_le (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) :
    ‖crossJetMap ℓ‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  exact fun D ↦ norm_crossJetMap_apply_le ℓ D hℓ

theorem norm_normalTensor_le (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) :
    ‖ℓ.smulRight ℓ‖ ≤ 1 := by
  rw [ContinuousLinearMap.norm_smulRight_apply]
  nlinarith [norm_nonneg ℓ]

theorem norm_liftFirstJet_sub_le (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1)
    (s : E → ℝ) (D : E → E →L[ℝ] ℝ) (x : E) (b : ℝ) :
    ‖liftFirstJet ℓ s D x - ℓ x • (b • ℓ)‖ ≤
      |ℓ x| * |s x - b| + (ℓ x) ^ 2 / 2 * ‖D x‖ := by
  have he : liftFirstJet ℓ s D x - ℓ x • (b • ℓ) =
      (ℓ x * (s x - b)) • ℓ + ((ℓ x) ^ 2 / 2) • D x := by
    ext v
    simp only [liftFirstJet, sub_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hq : 0 ≤ (ℓ x) ^ 2 / 2 := div_nonneg (sq_nonneg _) (by norm_num)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hq]
  have ht := mul_le_mul_of_nonneg_left hℓ
    (mul_nonneg (abs_nonneg (ℓ x)) (abs_nonneg (s x - b)))
  exact add_le_add (by simpa only [mul_one] using ht) le_rfl

theorem norm_liftSecondJet_sub_le (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1)
    (s : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (DD : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) (b : ℝ) :
    ‖liftSecondJet ℓ s D DD x - b • ℓ.smulRight ℓ‖ ≤
      |s x - b| + 2 * |ℓ x| * ‖D x‖ + (ℓ x) ^ 2 / 2 * ‖DD x‖ := by
  have he : liftSecondJet ℓ s D DD x - b • ℓ.smulRight ℓ =
      (s x - b) • ℓ.smulRight ℓ + (ℓ x) • crossJetMap ℓ (D x) +
        ((ℓ x) ^ 2 / 2) • DD x := by
    ext v w
    simp only [liftSecondJet, crossJetMap_apply, sub_apply, add_apply, smul_apply,
      smul_eq_mul, ContinuousLinearMap.smulRight_apply]
    ring
  rw [he]
  have ht := norm_add_le ((s x - b) • ℓ.smulRight ℓ + (ℓ x) • crossJetMap ℓ (D x))
    (((ℓ x) ^ 2 / 2) • DD x)
  have ht' := norm_add_le ((s x - b) • ℓ.smulRight ℓ) ((ℓ x) • crossJetMap ℓ (D x))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at ht'
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))] at ht
  have h1 := mul_le_mul_of_nonneg_left (norm_normalTensor_le ℓ hℓ) (abs_nonneg (s x - b))
  have h2 := mul_le_mul_of_nonneg_left (norm_crossJetMap_apply_le ℓ (D x) hℓ) (abs_nonneg (ℓ x))
  nlinarith

end OAI.Analysis.PDE.Schauder
