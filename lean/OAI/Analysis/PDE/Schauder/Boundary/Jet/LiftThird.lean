import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftNorms

noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance thirdDualNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance thirdDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance thirdBilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdTrilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdTrilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem differentiableAt_liftSecondJet
    (ℓ : E →L[ℝ] ℝ) (s : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    (DDD : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (x : E) (hs : HasFDerivAt s (D x) x)
    (hD : HasFDerivAt D (DD x) x) (hDD : HasFDerivAt DD (DDD x) x) :
    DifferentiableAt ℝ (liftSecondJet ℓ s D DD) x := by
  have h1 := hs.smul_const (ℓ.smulRight ℓ)
  have h2 := ℓ.hasFDerivAt.smul ((crossJetMap ℓ).hasFDerivAt.comp x hD)
  have h3 := (hasFDerivAt_halfSquare ℓ x).smul hDD
  convert! ((h1.add h2).add h3).differentiableAt using 1

theorem norm_fderiv_liftSecondJet_le
    (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1)
    (s : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    (DDD : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (x : E) (hs : HasFDerivAt s (D x) x)
    (hD : HasFDerivAt D (DD x) x) (hDD : HasFDerivAt DD (DDD x) x) :
    ‖fderiv ℝ (liftSecondJet ℓ s D DD) x‖ ≤
      3 * ‖D x‖ + 3 * |ℓ x| * ‖DD x‖ + (ℓ x) ^ 2 / 2 * ‖DDD x‖ := by
  let P := ℓ.smulRight ℓ
  let Q := crossJetMap ℓ
  let T1 := (D x).smulRight P
  let T2 := ℓ x • Q.comp (DD x) + ℓ.smulRight (Q (D x))
  let T3 := ((ℓ x) ^ 2 / 2) • DDD x + (ℓ x • ℓ).smulRight (DD x)
  have h1 : HasFDerivAt (fun y ↦ s y • P) T1 x := hs.smul_const P
  have h2 : HasFDerivAt (fun y ↦ ℓ y • Q (D y)) T2 x := by
    exact ℓ.hasFDerivAt.smul (Q.hasFDerivAt.comp x hD)
  have h3 : HasFDerivAt (fun y ↦ ((ℓ y) ^ 2 / 2) • DD y) T3 x := by
    exact (hasFDerivAt_halfSquare ℓ x).smul hDD
  have hall : HasFDerivAt (liftSecondJet ℓ s D DD) (T1 + T2 + T3) x := by
    convert! (h1.add h2).add h3 using 1
  rw [hall.fderiv]
  have hT1 : ‖T1‖ ≤ ‖D x‖ := by
    dsimp only [T1]
    rw [ContinuousLinearMap.norm_smulRight_apply]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (norm_normalTensor_le ℓ hℓ) (norm_nonneg (D x))
  have hQDD : ‖Q.comp (DD x)‖ ≤ 2 * ‖DD x‖ :=
    (ContinuousLinearMap.opNorm_comp_le Q (DD x)).trans
      (mul_le_mul_of_nonneg_right (norm_crossJetMap_le ℓ hℓ) (norm_nonneg (DD x)))
  have hT2 : ‖T2‖ ≤ 2 * |ℓ x| * ‖DD x‖ + 2 * ‖D x‖ := by
    have ht := norm_add_le (ℓ x • Q.comp (DD x)) (ℓ.smulRight (Q (D x)))
    rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply] at ht
    have ha := mul_le_mul_of_nonneg_left hQDD (abs_nonneg (ℓ x))
    have hb : ‖ℓ‖ * ‖Q (D x)‖ ≤ 2 * ‖D x‖ := by
      calc
        _ ≤ 1 * ‖Q (D x)‖ := mul_le_mul_of_nonneg_right hℓ (norm_nonneg _)
        _ ≤ 2 * ‖D x‖ := by simpa only [one_mul] using norm_crossJetMap_apply_le ℓ (D x) hℓ
    dsimp only [T2]
    nlinarith
  have hT3 : ‖T3‖ ≤ (ℓ x) ^ 2 / 2 * ‖DDD x‖ + |ℓ x| * ‖DD x‖ := by
    have ht := norm_add_le (((ℓ x) ^ 2 / 2) • DDD x) ((ℓ x • ℓ).smulRight (DD x))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num)),
      ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs] at ht
    have hh := mul_le_mul_of_nonneg_left hℓ (abs_nonneg (ℓ x))
    have hh' := mul_le_mul_of_nonneg_right hh (norm_nonneg (DD x))
    dsimp only [T3]
    nlinarith
  have ht := norm_add_le (T1 + T2) T3
  have ht' := norm_add_le T1 T2
  linarith

end OAI.Analysis.PDE.Schauder
