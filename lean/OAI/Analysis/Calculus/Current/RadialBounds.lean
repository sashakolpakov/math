import OAI.Analysis.Calculus.Current.Transverse

/-! Scale-invariant bounds for the derivative of the actual radial transverse field. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

theorem ratio_smul_real {d : ℕ} (c : ℝ) (hc : c ≠ 0) (z : Index d → ℂ) :
    ratio (c • z) = ratio z := by
  funext i
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  simp [ratio, Complex.real_smul, mul_div_mul_left _ _ hc']

theorem phi_smul_real {d : ℕ} (c : ℝ) (hc : c ≠ 0) (z : Index d → ℂ) :
    phi (c • z) = c • phi z := by
  have h := fiberDenominator_mul_height (c • z)
  rw [ratio_smul_real c hc z] at h
  have h' := fiberDenominator_mul_height z
  simp only [Pi.smul_apply, Complex.real_smul] at h ⊢
  linear_combination -h + (c : ℂ) * h'

theorem radialHeight_smul_real {d : ℕ} (c : ℝ) (hc : c ≠ 0) (z : Index d → ℂ) :
    radialHeight (c • z) = c • radialHeight z := by
  unfold radialHeight
  rw [ratio_smul_real c hc z, phi_smul_real c hc z]
  simp only [Pi.smul_apply, Complex.real_smul]
  ring

theorem fiberRadialField_smul_real {d : ℕ} (c : ℝ) (hc : c ≠ 0) (z : Index d → ℂ) :
    fiberRadialField (c • z) = c • fiberRadialField z := by
  funext i
  cases i with
  | none => exact radialHeight_smul_real c hc z
  | some i =>
    cases i with
    | none => exact radialHeight_smul_real c hc z
    | some i =>
      simp only [fiberRadialField, ratio_smul_real c hc z,
        radialHeight_smul_real c hc z, Pi.smul_apply, Complex.real_smul]
      ring

theorem homogeneous_one_fderiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (c : ℝ) (hc : c ≠ 0) (x : E)
    (hhom : ∀ q, f (c • q) = c • f q)
    (hf : DifferentiableAt ℝ f x) (hfc : DifferentiableAt ℝ f (c • x)) :
    fderiv ℝ f (c • x) = fderiv ℝ f x := by
  have hl := hfc.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul c)
  have hr : HasFDerivAt (fun q => f (c • q)) (c • fderiv ℝ f x) x := by
    simpa only [hhom, Pi.smul_def] using! hf.hasFDerivAt.const_smul c
  have he := hl.unique hr
  ext v
  have hev := congrArg (fun L : E →L[ℝ] F => L v) he
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul] at hev
  have := congrArg (fun w : F => c⁻¹ • w) hev
  simpa only [inv_smul_smul₀ hc] using this

theorem fiberRadialField_fderiv_smul {d : ℕ} (c : ℝ) (hc : c ≠ 0)
    (z : Index d → ℂ) (hY : z none ≠ 0) (hD : fiberDenominator (ratio z) ≠ 0) :
    fderiv ℝ (fiberRadialField : (Index d → ℂ) → Index d → ℂ) (c • z) =
      fderiv ℝ fiberRadialField z := by
  apply homogeneous_one_fderiv _ c hc z (fiberRadialField_smul_real c hc)
  · exact (contDiffAt_fiberRadialField z hY hD).differentiableAt (by norm_num)
  · apply (contDiffAt_fiberRadialField (c • z) _ _).differentiableAt (by norm_num)
    · intro hz
      have hh := congrArg norm hz
      simp only [Pi.smul_apply, norm_smul, norm_zero] at hh
      exact (mul_ne_zero (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hY)) hh
    · simpa only [ratio_smul_real c hc z] using hD

theorem fiber_norm_eq_height {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (ha : 0 < a) (hay : a ≤ ‖z none‖) (hr : fiberDefining (1 / 10) a z ≤ 0) :
    ‖z‖ = ‖z none‖ := by
  have hY : z none ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (ha.trans_le hay))
  have hQ := (norm_fiberQuadratic_le (ratio z)).trans
    (fiber_ratio_bound (1 / 10) a z (by norm_num) hr)
  have hP := fiber_phase_norm_le a ha z hr
  have hS : z (some none) = phi z - z none * fiberQuadratic (ratio z) / 2 := by
    have h := fiberDenominator_mul_height z
    unfold fiberDenominator at h
    linear_combination h
  apply le_antisymm _ (norm_le_pi_norm z none)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  cases i with
  | none => exact le_rfl
  | some i =>
    cases i with
    | none =>
      rw [hS]
      calc
        _ ≤ ‖phi z‖ + ‖z none‖ * ‖fiberQuadratic (ratio z)‖ / 2 := by
          convert norm_sub_le (phi z) (z none * fiberQuadratic (ratio z) / 2) using 1 ;
            simp []
        _ ≤ a / 10 + ‖z none‖ * (1 / 10 : ℝ) ^ 2 / 2 := by
          gcongr
        _ ≤ ‖z none‖ := by nlinarith [norm_nonneg (z none)]
    | some i =>
      have he : z (some (some i)) = ratio z i * z none := by simp [ratio, hY]
      rw [he, norm_mul]
      exact (mul_le_mul_of_nonneg_right (fiber_ratio_coordinate_le_one a z hr i)
        (norm_nonneg _)).trans_eq (one_mul _)

def normalizedRadialSet (d : ℕ) : Set (Index d → ℂ) :=
  {z | ‖z‖ ≤ 1 ∧ ‖z none‖ = 1 ∧ (∑ i : Fin d, ‖z (some (some i))‖ ^ 2) ≤ (1 / 10 : ℝ) ^ 2}

theorem isCompact_normalizedRadialSet (d : ℕ) : IsCompact (normalizedRadialSet d) := by
  have hp : Continuous (fun z : Index d → ℂ => ∑ i : Fin d, ‖z (some (some i))‖ ^ 2) := by fun_prop
  have hc : IsClosed (normalizedRadialSet d) := by
    apply IsClosed.inter (isClosed_le continuous_norm continuous_const)
    exact (isClosed_eq (continuous_apply none |>.norm) continuous_const).inter
      (isClosed_le hp continuous_const)
  apply (isCompact_closedBall (0 : Index d → ℂ) 1).of_isClosed_subset hc
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1

theorem normalizedRadialSet_domain {d : ℕ} {z : Index d → ℂ}
    (hz : z ∈ normalizedRadialSet d) : z none ≠ 0 ∧ fiberDenominator (ratio z) ≠ 0 := by
  have hY : z none ≠ 0 := by
    intro h
    have := hz.2.1
    simp [h] at this
  refine ⟨hY, fiberDenominator_ne_zero _ ?_⟩
  have hs : (∑ i : Fin d, ‖ratio z i‖ ^ 2) = ∑ i : Fin d, ‖z (some (some i))‖ ^ 2 := by
    simp [ratio, hz.2.1]
  rw [hs]
  exact lt_of_le_of_lt hz.2.2 (by norm_num)

theorem normalize_mem_radialSet {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (ha : 0 < a) (hay : a ≤ ‖z none‖) (hr : fiberDefining (1 / 10) a z ≤ 0) :
    ‖z none‖⁻¹ • z ∈ normalizedRadialSet d := by
  have hy : 0 < ‖z none‖ := ha.trans_le hay
  have hc : ‖z none‖⁻¹ ≠ 0 := inv_ne_zero hy.ne'
  refine ⟨?_, ?_, ?_⟩
  · simp [norm_smul, fiber_norm_eq_height a z ha hay hr, hy.ne']
  · simp [Pi.smul_apply, hy.ne']
  · have hb := fiber_ratio_bound (1 / 10) a z (by norm_num) hr
    have hi (i : Fin d) : ‖(‖z none‖⁻¹ • z) (some (some i))‖ = ‖ratio z i‖ := by
      simp [Pi.smul_apply, ratio, div_eq_mul_inv, mul_comm]
    simpa only [hi] using hb

theorem fiberRadialField_fderiv_uniform_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (z : Index d → ℂ),
      0 < a → a ≤ ‖z none‖ → fiberDefining (1 / 10) a z ≤ 0 →
      ‖fderiv ℝ (fiberRadialField : (Index d → ℂ) → Index d → ℂ) z‖ ≤ C := by
  have hcont : ContinuousOn
      (fun z => ‖fderiv ℝ (fiberRadialField : (Index d → ℂ) → Index d → ℂ) z‖)
      (normalizedRadialSet d) := by
    intro z hz
    obtain ⟨hY, hD⟩ := normalizedRadialSet_domain hz
    exact ((contDiffAt_fiberRadialField z hY hD).continuousAt_fderiv (by norm_num)).norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_normalizedRadialSet d).exists_bound_of_continuousOn hcont
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro a z ha hay hr
  have hy : 0 < ‖z none‖ := ha.trans_le hay
  have hY := norm_ne_zero_iff.mp hy.ne'
  have hz := normalize_mem_radialSet a z ha hay hr
  have hb := hB _ hz
  rw [fiberRadialField_fderiv_smul _ (inv_ne_zero hy.ne') z hY
    (fiberDenominator_ne_zero_on_fiber a z hr)] at hb
  exact (le_abs_self _).trans (hb.trans (by linarith [le_abs_self B]))

end OAI.Analysis.Calculus.Current
