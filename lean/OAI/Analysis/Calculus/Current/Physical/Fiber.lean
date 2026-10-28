import OAI.Analysis.Calculus.Current.RadialBounds

/-! The fixed physical imaginary-time fiber, with `Z=(Y+S₁)/√2`. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

def physicalLift (d : ℕ) : (Option (Fin d) → ℂ) →L[ℝ] (Index d → ℂ) :=
  ContinuousLinearMap.pi fun b => match b with
    | none => (Real.sqrt 2)⁻¹ • ContinuousLinearMap.proj none
    | some none => (Real.sqrt 2)⁻¹ • ContinuousLinearMap.proj none
    | some (some i) => ContinuousLinearMap.proj (some i)

def physicalProjection (d : ℕ) : (Index d → ℂ) →L[ℝ] (Option (Fin d) → ℂ) :=
  ContinuousLinearMap.pi fun b => match b with
    | none => Real.sqrt 2 • ContinuousLinearMap.proj none
    | some i => ContinuousLinearMap.proj (some (some i))

def physicalTimeOffset {d : ℕ} (τ : ℂ) : Index d → ℂ
  | none => (Real.sqrt 2)⁻¹ • τ
  | some none => -(Real.sqrt 2)⁻¹ • τ
  | some (some _) => 0

def physicalEmbedding {d : ℕ} (τ : ℂ) (q : Option (Fin d) → ℂ) : Index d → ℂ :=
  physicalLift d q + physicalTimeOffset τ

def physicalFiberDefining {d : ℕ} (w a : ℝ) (τ : ℂ) (q : Option (Fin d) → ℂ) : ℝ :=
  fiberDefining w a (physicalEmbedding τ q)

def physicalRadialField {d : ℕ} (τ : ℂ) (q : Option (Fin d) → ℂ) : Option (Fin d) → ℂ :=
  physicalProjection d (fiberRadialField (physicalEmbedding τ q))

theorem imaginaryTime_physicalEmbedding {d : ℕ} (τ : ℂ) (q : Option (Fin d) → ℂ) :
    imaginaryTime (physicalEmbedding τ q) = τ := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp only [imaginaryTime, physicalEmbedding, physicalLift, physicalTimeOffset,
    ContinuousLinearMap.pi_apply, smul_apply, ContinuousLinearMap.proj_apply,
    Pi.add_apply, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_neg]
  field_simp
  linear_combination -τ * hs

theorem hasFDerivAt_physicalEmbedding {d : ℕ} (τ : ℂ) (q : Option (Fin d) → ℂ) :
    HasFDerivAt (physicalEmbedding τ) (physicalLift d) q :=
  (physicalLift d).hasFDerivAt.add_const _

theorem contDiff_physicalEmbedding {d : ℕ} (τ : ℂ) :
    ContDiff ℝ ⊤ (physicalEmbedding (d := d) τ) :=
  (physicalLift d).contDiff.add contDiff_const

theorem physicalLift_physicalRadialField {d : ℕ} (τ : ℂ) (q : Option (Fin d) → ℂ) :
    physicalLift d (physicalRadialField τ q) = fiberRadialField (physicalEmbedding τ q) := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  funext b
  cases b with
  | none => simp [physicalLift, physicalProjection, physicalRadialField, hs]
  | some b =>
    cases b with
    | none => simp [physicalLift, physicalProjection, physicalRadialField, fiberRadialField, hs]
    | some i => rfl

theorem fderiv_physicalFiberDefining_radial {d : ℕ} (w a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (hY : physicalEmbedding τ q none ≠ 0)
    (hD : fiberDenominator (ratio (physicalEmbedding τ q)) ≠ 0) :
    fderiv ℝ (physicalFiberDefining w a τ) q (physicalRadialField τ q) =
      2 * (physicalFiberDefining w a τ q + 1) := by
  have hr := (contDiffAt_fiberDefining w a (physicalEmbedding τ q) hY).differentiableAt (by norm_num)
  have he := hasFDerivAt_physicalEmbedding τ q
  have hh := hr.hasFDerivAt.comp q he
  rw [show physicalFiberDefining w a τ = fiberDefining w a ∘ physicalEmbedding τ from rfl,
    hh.fderiv]
  simpa only [ContinuousLinearMap.comp_apply, physicalLift_physicalRadialField,
    Function.comp_apply] using fderiv_fiberDefining_radial w a (physicalEmbedding τ q) hY hD

theorem physical_radial_transverse_coefficient {d : ℕ} (a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (hY : physicalEmbedding τ q none ≠ 0)
    (hr : physicalFiberDefining (1 / 10) a τ q ≤ 0) :
    1 ≤ fderiv ℝ (physicalFiberDefining (1 / 10) a τ) q (physicalRadialField τ q) +
      (physicalFiberDefining (1 / 10) a τ q) ^ 2 := by
  rw [fderiv_physicalFiberDefining_radial _ _ _ _ hY
    (fiberDenominator_ne_zero_on_fiber _ _ hr)]
  nlinarith [sq_nonneg (physicalFiberDefining (1 / 10) a τ q + 1)]

theorem contDiffAt_physicalRadialField {d : ℕ} (τ : ℂ) (q : Option (Fin d) → ℂ)
    (hY : physicalEmbedding τ q none ≠ 0)
    (hD : fiberDenominator (ratio (physicalEmbedding τ q)) ≠ 0) :
    ContDiffAt ℝ ⊤ (physicalRadialField τ) q :=
  (physicalProjection d).contDiff.contDiffAt.comp q
    ((contDiffAt_fiberRadialField _ hY hD).comp q (contDiff_physicalEmbedding τ).contDiffAt)

theorem contDiffAt_physicalFiberDefining {d : ℕ} (w a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (hY : physicalEmbedding τ q none ≠ 0) :
    ContDiffAt ℝ ⊤ (physicalFiberDefining w a τ) q :=
  (contDiffAt_fiberDefining w a _ hY).comp q (contDiff_physicalEmbedding τ).contDiffAt

theorem physicalFiberDefining_ge_neg_one {d : ℕ} (w a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) : -1 ≤ physicalFiberDefining w a τ q := by
  have : 0 ≤ ∑ i, ‖fiberMap w a (physicalEmbedding τ q) i‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change -1 ≤ (∑ i, ‖fiberMap w a (physicalEmbedding τ q) i‖ ^ 2) - 1
  linarith

theorem physicalFiberDefining_regular_boundary {d : ℕ} (a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (hY : physicalEmbedding τ q none ≠ 0)
    (hr : physicalFiberDefining (1 / 10) a τ q = 0) :
    fderiv ℝ (physicalFiberDefining (1 / 10) a τ) q ≠ 0 := by
  have hd := fderiv_physicalFiberDefining_radial (1 / 10) a τ q hY
    (fiberDenominator_ne_zero_on_fiber a (physicalEmbedding τ q) hr.le)
  intro hz
  rw [hz, zero_apply, hr] at hd
  norm_num at hd

theorem physicalLift_norm_le (d : ℕ) : ‖physicalLift d‖ ≤ 1 := by
  have hs : 1 ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro b
  have h0 : ‖(Real.sqrt 2)⁻¹ • v none‖ ≤ ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    calc
      _ ≤ 1 * ‖v none‖ := mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hs) (norm_nonneg _)
      _ ≤ ‖v‖ := by simpa only [one_mul] using norm_le_pi_norm v none
  cases b with
  | none => exact h0
  | some b =>
    cases b with
    | none => exact h0
    | some i => exact norm_le_pi_norm v (some i)

theorem physicalProjection_norm_le (d : ℕ) : ‖physicalProjection d‖ ≤ 2 := by
  have hs : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro b
  cases b with
  | none =>
    change ‖Real.sqrt 2 • v none‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul hs (norm_le_pi_norm v none) (norm_nonneg _) (by norm_num)
  | some i =>
    exact (norm_le_pi_norm v (some (some i))).trans (by nlinarith [norm_nonneg v])

theorem physicalRadialField_uniform_bounds (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (τ : ℂ) (q : Option (Fin d) → ℂ),
      0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 → physicalFiberDefining (1 / 10) a τ q ≤ 0 →
      ‖physicalRadialField τ q‖ ≤ 48 ∧ ‖fderiv ℝ (physicalRadialField τ) q‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := fiberRadialField_fderiv_uniform_bound d
  refine ⟨2 * B, by positivity, ?_⟩
  intro a τ q ha ht ht' hr
  let z := physicalEmbedding τ q
  have htime : imaginaryTime z = τ := imaginaryTime_physicalEmbedding τ q
  have hay : a ≤ ‖z none‖ := fiber_height_ge_scale a ha z hr (by simpa only [htime] using ht)
  have hY : z none ≠ 0 := norm_ne_zero_iff.mp (ha.trans_le hay).ne'
  have hD := fiberDenominator_ne_zero_on_fiber a z hr
  have hnorm : ‖fiberRadialField z‖ ≤ 24 := fiberRadialField_norm_le_on_time_strip a z ha hr
    (by simpa only [htime] using ht) (by simpa only [htime] using ht')
  constructor
  · exact ((physicalProjection d).le_opNorm _).trans
      ((mul_le_mul (physicalProjection_norm_le d) hnorm (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))
  · have hv := (contDiffAt_fiberRadialField z hY hD).differentiableAt (by norm_num)
    have hh := (physicalProjection d).hasFDerivAt.comp q
      (hv.hasFDerivAt.comp q (hasFDerivAt_physicalEmbedding τ q))
    change ‖fderiv ℝ (physicalProjection d ∘ fiberRadialField ∘ physicalEmbedding τ) q‖ ≤ 2 * B
    rw [hh.fderiv]
    calc
      _ ≤ ‖physicalProjection d‖ * (‖fderiv ℝ fiberRadialField z‖ * ‖physicalLift d‖) :=
        ((physicalProjection d).opNorm_comp_le _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 2 * (B * 1) := by
        gcongr
        · exact physicalProjection_norm_le d
        · exact hb a z ha hay hr
        · exact physicalLift_norm_le d
      _ = _ := by ring

theorem physicalFiberDefining_fderiv_norm_lower {d : ℕ} (a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (ha : 0 < a) (ht : a ≤ ‖τ‖) (ht' : ‖τ‖ ≤ 4)
    (hr : physicalFiberDefining (1 / 10) a τ q ≤ 0)
    (hr' : -(1 / 2 : ℝ) ≤ physicalFiberDefining (1 / 10) a τ q) :
    (1 / 48 : ℝ) ≤ ‖fderiv ℝ (physicalFiberDefining (1 / 10) a τ) q‖ := by
  have hy := fiber_height_ge_scale a ha (physicalEmbedding τ q) hr
    (by simpa only [imaginaryTime_physicalEmbedding] using ht)
  have hY : physicalEmbedding τ q none ≠ 0 := norm_ne_zero_iff.mp (ha.trans_le hy).ne'
  have hd := fderiv_physicalFiberDefining_radial (1 / 10) a τ q hY
    (fiberDenominator_ne_zero_on_fiber a _ hr)
  obtain ⟨C, hC, hb⟩ := physicalRadialField_uniform_bounds d
  have hv := (hb a τ q ha ht ht' hr).1
  have hn := (fderiv ℝ (physicalFiberDefining (1 / 10) a τ) q).le_opNorm (physicalRadialField τ q)
  rw [hd, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hn
  have hm := mul_le_mul_of_nonneg_left hv
    (norm_nonneg (fderiv ℝ (physicalFiberDefining (1 / 10) a τ) q))
  nlinarith

end OAI.Analysis.Calculus.Current
