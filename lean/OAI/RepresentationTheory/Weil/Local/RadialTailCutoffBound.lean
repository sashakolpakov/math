import OAI.RepresentationTheory.Weil.Local.PowerWeightBounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # Radial Tail Cutoff Bound -/

namespace OAI.RepresentationTheory.Weil.Local.RadialTailCutoffBound.Construction

noncomputable section

section

/-! A fixed smooth radial cutoff and compactly supported derivatives. -/

open Set Filter
open scoped _root_.Topology ContDiff

def radialCutoffBase (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

theorem radialCutoffBase_contDiff : ContDiff ℝ ∞ radialCutoffBase :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem radialCutoffBase_nonneg (t : ℝ) : 0 ≤ radialCutoffBase t := Real.smoothTransition.nonneg _

theorem radialCutoffBase_le_one (t : ℝ) : radialCutoffBase t ≤ 1 := Real.smoothTransition.le_one _

theorem radialCutoffBase_zero {t : ℝ} (ht : t ≤ 1) : radialCutoffBase t = 0 :=
  Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ht)

theorem radialCutoffBase_one {t : ℝ} (ht : 2 ≤ t) : radialCutoffBase t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem radialCutoffBase_deriv_zero {t : ℝ} (ht : t ∉ Icc (1 : ℝ) 2) :
    deriv radialCutoffBase t = 0 := by
  have hsplit : t < 1 ∨ 2 < t := by simpa only [mem_Icc, not_and_or, not_le] using ht
  rcases hsplit with ht | ht
  · have heq : radialCutoffBase =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds ht] with y hy
      exact radialCutoffBase_zero hy.le
    simpa only [deriv_const] using heq.deriv_eq
  · have heq : radialCutoffBase =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds ht] with y hy
      exact radialCutoffBase_one hy.le
    simpa only [deriv_const] using heq.deriv_eq

theorem radialCutoffBase_deriv_tsupport : tsupport (deriv radialCutoffBase) ⊆ Icc (1 : ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hh
  exact ht (radialCutoffBase_deriv_zero hh)

theorem radialCutoffBase_deriv_compact : HasCompactSupport (deriv radialCutoffBase) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) radialCutoffBase_deriv_tsupport

theorem radialCutoffBase_second_deriv_zero {t : ℝ} (ht : t ∉ Icc (1 : ℝ) 2) :
    deriv (deriv radialCutoffBase) t = 0 :=
  deriv_of_notMem_tsupport (fun h => ht (radialCutoffBase_deriv_tsupport h))

theorem radialCutoffBase_derivative_bounds : ∃ C : ℝ, 0 < C ∧
    (∀ t, |deriv radialCutoffBase t| ≤ C) ∧ (∀ t, |deriv (deriv radialCutoffBase) t| ≤ C) := by
  have h1 : Continuous (deriv radialCutoffBase) := radialCutoffBase_contDiff.continuous_deriv (by simp)
  have h2 : Continuous (deriv (deriv radialCutoffBase)) :=
    (radialCutoffBase_contDiff.iterate_deriv 2).continuous
  obtain ⟨C1, hC1⟩ := radialCutoffBase_deriv_compact.exists_bound_of_continuous h1
  obtain ⟨C2, hC2⟩ := radialCutoffBase_deriv_compact.deriv.exists_bound_of_continuous h2
  refine ⟨max (max C1 C2) 0 + 1, by positivity, ?_, ?_⟩
  · intro t
    exact (hC1 t).trans (by linarith [le_max_left C1 C2, le_max_left (max C1 C2) 0])
  · intro t
    exact (hC2 t).trans (by linarith [le_max_right C1 C2, le_max_left (max C1 C2) 0])

end

section

/-! Rescaled radial cutoffs and bounds adapted to the squared radius. -/

open Set

def radialCutoff (R t : ℝ) : ℝ := radialCutoffBase (t / R)

def radialCutoffDerivative (R t : ℝ) : ℝ := R⁻¹ * deriv radialCutoffBase (t / R)

def radialCutoffSecondDerivative (R t : ℝ) : ℝ := R⁻¹ ^ 2 * deriv (deriv radialCutoffBase) (t / R)

theorem radialCutoff_hasDerivAt (R t : ℝ) :
    HasDerivAt (radialCutoff R) (radialCutoffDerivative R t) t := by
  have hd := ((radialCutoffBase_contDiff.differentiable (by simp) (t / R)).hasDerivAt).comp t
    ((hasDerivAt_id t).div_const R)
  dsimp only [id_eq] at hd
  convert! hd using 1
  unfold radialCutoffDerivative
  ring

theorem radialCutoffDerivative_hasDerivAt (R t : ℝ) :
    HasDerivAt (radialCutoffDerivative R) (radialCutoffSecondDerivative R t) t := by
  have hc2 : ContDiff ℝ 2 radialCutoffBase :=
    radialCutoffBase_contDiff.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hdiff : Differentiable ℝ (deriv radialCutoffBase) := hc2.differentiable_deriv_two
  have hd := (((hdiff (t / R)).hasDerivAt).comp t ((hasDerivAt_id t).div_const R)).const_mul R⁻¹
  dsimp only [id_eq] at hd
  convert! hd using 1
  unfold radialCutoffSecondDerivative
  ring

theorem radialCutoff_nonneg (R t : ℝ) : 0 ≤ radialCutoff R t := radialCutoffBase_nonneg _

theorem radialCutoff_le_one (R t : ℝ) : radialCutoff R t ≤ 1 := radialCutoffBase_le_one _

theorem radialCutoff_zero (R t : ℝ) (hR : 0 < R) (ht : t ≤ R) : radialCutoff R t = 0 :=
  radialCutoffBase_zero ((div_le_one hR).mpr ht)

theorem radialCutoff_one (R t : ℝ) (hR : 0 < R) (ht : 2 * R ≤ t) : radialCutoff R t = 1 :=
  radialCutoffBase_one ((le_div_iff₀ hR).mpr ht)

theorem radialCutoff_derivatives_zero (R t : ℝ) (hR : 0 < R) (ht : t ∉ Icc R (2 * R)) :
    radialCutoffDerivative R t = 0 ∧ radialCutoffSecondDerivative R t = 0 := by
  have hq : t / R ∉ Icc (1 : ℝ) 2 := by
    intro hh
    apply ht
    exact ⟨by simpa only [one_mul] using (le_div_iff₀ hR).mp hh.1, (div_le_iff₀ hR).mp hh.2⟩
  simp only [radialCutoffDerivative, radialCutoffSecondDerivative,
    radialCutoffBase_deriv_zero hq, radialCutoffBase_second_deriv_zero hq, mul_zero, and_self]

theorem radialCutoff_derivative_bounds : ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ t : ℝ, 0 < t →
    |radialCutoffDerivative R t| ≤ 2 * C / t ∧
      |radialCutoffSecondDerivative R t| ≤ 4 * C / t ^ 2 := by
  obtain ⟨C, hC, h1, h2⟩ := radialCutoffBase_derivative_bounds
  refine ⟨C, hC, fun R hR t ht => ?_⟩
  by_cases hmem : t ∈ Icc R (2 * R)
  · have hd1 : |radialCutoffDerivative R t| ≤ C / R := by
      rw [radialCutoffDerivative, abs_mul, abs_of_pos (inv_pos.mpr hR),
        div_eq_mul_inv C R, mul_comm C]
      exact mul_le_mul_of_nonneg_left (h1 _) (inv_nonneg.mpr hR.le)
    have hd2 : |radialCutoffSecondDerivative R t| ≤ C / R ^ 2 := by
      rw [radialCutoffSecondDerivative, abs_mul, abs_of_nonneg (sq_nonneg _),
        div_eq_mul_inv C (R ^ 2), ← inv_pow, mul_comm C]
      exact mul_le_mul_of_nonneg_left (h2 _) (sq_nonneg _)
    constructor
    · apply hd1.trans
      apply (div_le_div_iff₀ hR ht).mpr
      nlinarith [mul_le_mul_of_nonneg_left hmem.2 hC.le]
    · apply hd2.trans
      apply (div_le_div_iff₀ (sq_pos_of_pos hR) (sq_pos_of_pos ht)).mpr
      have hs := (sq_le_sq₀ ht.le (by positivity : 0 ≤ 2 * R)).mpr hmem.2
      nlinarith [mul_le_mul_of_nonneg_left hs hC.le]
  · obtain ⟨h1, h2⟩ := radialCutoff_derivatives_zero R t hR hmem
    rw [h1, h2, abs_zero]
    constructor <;> positivity

end

section

/-! A smooth damped inverse-radius weight supported away from the origin. -/

open Filter Set
open scoped _root_.Topology

def radialTailWeight (s ε R t : ℝ) : ℝ := radialCutoff R t * RealPower.Construction.realPowerWeight s ε t

def radialTailWeightDerivative (s ε R t : ℝ) : ℝ :=
  radialCutoffDerivative R t * RealPower.Construction.realPowerWeight s ε t +
    radialCutoff R t * RealPower.Construction.realPowerWeightDerivative s ε t

def radialTailWeightSecondDerivative (s ε R t : ℝ) : ℝ :=
  radialCutoffSecondDerivative R t * RealPower.Construction.realPowerWeight s ε t +
    2 * radialCutoffDerivative R t * RealPower.Construction.realPowerWeightDerivative s ε t +
    radialCutoff R t * PowerWeightBounds.Construction.realPowerWeightSecondDerivative s ε t

theorem radialTailWeight_zero (s ε R t : ℝ) (hR : 0 < R) (ht : t < R) :
    radialTailWeight s ε R t = 0 := by
  rw [radialTailWeight, radialCutoff_zero R t hR ht.le, zero_mul]

theorem radialTailWeightDerivative_zero (s ε R t : ℝ) (hR : 0 < R) (ht : t < R) :
    radialTailWeightDerivative s ε R t = 0 := by
  have hout : t ∉ Icc R (2 * R) := fun h => ht.not_ge h.1
  rw [radialTailWeightDerivative, (radialCutoff_derivatives_zero R t hR hout).1,
    radialCutoff_zero R t hR ht.le, zero_mul, zero_mul, add_zero]

theorem radialTailWeightSecondDerivative_zero (s ε R t : ℝ) (hR : 0 < R) (ht : t < R) :
    radialTailWeightSecondDerivative s ε R t = 0 := by
  have hout : t ∉ Icc R (2 * R) := fun h => ht.not_ge h.1
  obtain ⟨h1, h2⟩ := radialCutoff_derivatives_zero R t hR hout
  simp only [radialTailWeightSecondDerivative, h1, h2, radialCutoff_zero R t hR ht.le,
    zero_mul, mul_zero, add_zero]

theorem radialTailWeight_hasDerivAt (s ε R : ℝ) (hR : 0 < R) (t : ℝ) :
    HasDerivAt (radialTailWeight s ε R) (radialTailWeightDerivative s ε R t) t := by
  by_cases ht : 0 < t
  · exact (radialCutoff_hasDerivAt R t).mul (RealPower.Construction.realPowerWeight_hasDerivAt s ε t ht)
  · have htR : t < R := (le_of_not_gt ht).trans_lt hR
    have heq : radialTailWeight s ε R =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds htR] with x hx
      exact radialTailWeight_zero s ε R x hR hx
    rw [radialTailWeightDerivative_zero s ε R t hR htR]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq

theorem radialTailWeightDerivative_hasDerivAt (s ε R : ℝ) (hR : 0 < R) (t : ℝ) :
    HasDerivAt (radialTailWeightDerivative s ε R) (radialTailWeightSecondDerivative s ε R t) t := by
  by_cases ht : 0 < t
  · have hd := ((radialCutoffDerivative_hasDerivAt R t).mul
      (RealPower.Construction.realPowerWeight_hasDerivAt s ε t ht)).add
        ((radialCutoff_hasDerivAt R t).mul (PowerWeightBounds.Construction.realPowerWeightDerivative_hasDerivAt s ε t ht))
    convert! hd using 1
    unfold radialTailWeightSecondDerivative
    ring
  · have htR : t < R := (le_of_not_gt ht).trans_lt hR
    have heq : radialTailWeightDerivative s ε R =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds htR] with x hx
      exact radialTailWeightDerivative_zero s ε R x hR hx
    rw [radialTailWeightSecondDerivative_zero s ε R t hR htR]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq

theorem radialTailWeight_laplacian (s ε R t : ℝ) :
    t * radialTailWeightSecondDerivative s ε R t + radialTailWeightDerivative s ε R t =
      radialCutoff R t * (t * PowerWeightBounds.Construction.realPowerWeightSecondDerivative s ε t + RealPower.Construction.realPowerWeightDerivative s ε t) +
      2 * t * radialCutoffDerivative R t * RealPower.Construction.realPowerWeightDerivative s ε t +
      (t * radialCutoffSecondDerivative R t + radialCutoffDerivative R t) * RealPower.Construction.realPowerWeight s ε t := by
  unfold radialTailWeightSecondDerivative radialTailWeightDerivative
  ring

end

section

/-! A uniform integrable bound for the radial Laplacian of the damped cutoff weight. -/

theorem radialTailWeight_laplacian_bound : ∃ C : ℝ, 0 < C ∧
    ∀ s ε R t : ℝ, 0 < s → s ≤ 1 → 0 ≤ ε → 0 < R → 0 < t →
      |t * radialTailWeightSecondDerivative s ε R t + radialTailWeightDerivative s ε R t| ≤ C / t ^ 2 := by
  obtain ⟨C, hC, hcut⟩ := radialCutoff_derivative_bounds
  refine ⟨2 + 10 * C, by positivity, fun s ε R t hs hs1 hε hR ht => ?_⟩
  obtain ⟨hcut1, hcut2⟩ := hcut R hR t ht
  have hw : |RealPower.Construction.realPowerWeight s ε t| ≤ 1 / t := by
    rw [abs_of_nonneg (RealPower.Construction.realPowerWeight_nonneg s ε t ht), one_div]
    exact RealPower.Construction.realPowerWeight_le_inverse s ε t hε ht
  have hw1 := PowerWeightBounds.Construction.realPowerWeightDerivative_abs_le s ε t hs hs1 hε ht
  have hL0 := PowerWeightBounds.Construction.realPowerWeight_radial_laplacian_nonneg s ε t hs hs1 hε ht
  have hL := PowerWeightBounds.Construction.realPowerWeight_radial_laplacian_le s ε t hs hs1 hε ht
  have hA : |radialCutoff R t *
      (t * PowerWeightBounds.Construction.realPowerWeightSecondDerivative s ε t + RealPower.Construction.realPowerWeightDerivative s ε t)| ≤ 2 / t ^ 2 := by
    rw [abs_mul, abs_of_nonneg (radialCutoff_nonneg R t), abs_of_nonneg hL0]
    calc
      _ ≤ 1 * (2 / t ^ 2) := mul_le_mul (radialCutoff_le_one R t) hL hL0 (by norm_num)
      _ = _ := one_mul _
  have hB : |2 * t * radialCutoffDerivative R t * RealPower.Construction.realPowerWeightDerivative s ε t| ≤
      4 * C / t ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos ht]
    calc
      _ ≤ 2 * t * (2 * C / t) * (1 / t ^ 2) := by gcongr
      _ = _ := by field_simp; ring
  have hD : |t * radialCutoffSecondDerivative R t + radialCutoffDerivative R t| ≤
      t * (4 * C / t ^ 2) + 2 * C / t := by
    calc
      _ ≤ |t * radialCutoffSecondDerivative R t| + |radialCutoffDerivative R t| := abs_add_le _ _
      _ = t * |radialCutoffSecondDerivative R t| + |radialCutoffDerivative R t| := by
        rw [abs_mul, abs_of_pos ht]
      _ ≤ _ := by gcongr
  have hE : |(t * radialCutoffSecondDerivative R t + radialCutoffDerivative R t) *
      RealPower.Construction.realPowerWeight s ε t| ≤ 6 * C / t ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ (t * (4 * C / t ^ 2) + 2 * C / t) * (1 / t) :=
        mul_le_mul hD hw (abs_nonneg _) (by positivity)
      _ = _ := by field_simp; ring
  rw [radialTailWeight_laplacian]
  calc
    _ ≤ (|radialCutoff R t *
        (t * PowerWeightBounds.Construction.realPowerWeightSecondDerivative s ε t + RealPower.Construction.realPowerWeightDerivative s ε t)| +
        |2 * t * radialCutoffDerivative R t * RealPower.Construction.realPowerWeightDerivative s ε t|) +
        |(t * radialCutoffSecondDerivative R t + radialCutoffDerivative R t) * RealPower.Construction.realPowerWeight s ε t| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 / t ^ 2 + 4 * C / t ^ 2 + 6 * C / t ^ 2 := add_le_add (add_le_add hA hB) hE
    _ = (2 + 10 * C) / t ^ 2 := by ring

end

/-! A product estimate for radial Laplacians, used with an additional outer cutoff. -/

theorem radial_laplacian_product_bound
    (t w w' w'' c c' c'' A B D P Q : ℝ)
    (ht : 0 < t) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hw : |w| ≤ A / t) (hw' : |w'| ≤ B / t ^ 2)
    (hL : |t * w'' + w'| ≤ D / t ^ 2)
    (hc' : |c'| ≤ P / t) (hc'' : |c''| ≤ Q / t ^ 2) :
    |c * (t * w'' + w') + 2 * t * c' * w' + (t * c'' + c') * w| ≤
      (D + 2 * P * B + (Q + P) * A) / t ^ 2 := by
  have h1 : |c * (t * w'' + w')| ≤ D / t ^ 2 := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc
      _ ≤ 1 * (D / t ^ 2) := mul_le_mul hc1 hL (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have h2 : |2 * t * c' * w'| ≤ 2 * P * B / t ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos ht]
    calc
      _ ≤ 2 * t * (P / t) * (B / t ^ 2) := by gcongr
      _ = _ := by field_simp
  have h3 : |t * c'' + c'| ≤ t * (Q / t ^ 2) + P / t := by
    calc
      _ ≤ |t * c''| + |c'| := abs_add_le _ _
      _ = t * |c''| + |c'| := by rw [abs_mul, abs_of_pos ht]
      _ ≤ _ := by gcongr
  have h4 : |(t * c'' + c') * w| ≤ (Q + P) * A / t ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ (t * (Q / t ^ 2) + P / t) * (A / t) :=
        mul_le_mul h3 hw (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ (|c * (t * w'' + w')| + |2 * t * c' * w'|) + |(t * c'' + c') * w| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ D / t ^ 2 + 2 * P * B / t ^ 2 + (Q + P) * A / t ^ 2 :=
      add_le_add (add_le_add h1 h2) h4
    _ = _ := by ring

end

end OAI.RepresentationTheory.Weil.Local.RadialTailCutoffBound.Construction
