import OAI.Analysis.PDE.Concentration.Separable
import OAI.Analysis.PDE.Concentration.EscapeBarrier
import OAI.Analysis.PDE.Concentration.TimeWeight
import OAI.Analysis.PDE.Concentration.Cylinder.Boundary
import OAI.Analysis.PDE.Concentration.Maximum

namespace OAI.Analysis.PDE.Concentration

open Set Filter Laplacian InnerProductSpace
open scoped ContDiff Topology

theorem cylinderTimeWeight_second_deriv (t : ℝ) :
    deriv (deriv cylinderTimeWeight) t = -cylinderTimeWeight t / 100 := by
  have he : deriv cylinderTimeWeight = cylinderTimeWeightDeriv :=
    funext (fun s => (hasDerivAt_cylinderTimeWeight s).deriv)
  rw [he, (hasDerivAt_cylinderTimeWeightDeriv t).deriv]

noncomputable def cylinderEscapeFunction (ρ : ℝ) : CylinderSpace → ℝ :=
  cylinderSeparable cylinderTimeWeight (cylinderEscapeBarrier ρ)

theorem contDiffOn_cylinderEscapeFunction (ρ : ℝ) :
    ContDiffOn ℝ ∞ (cylinderEscapeFunction ρ) cylinderAxisComplement :=
  contDiffOn_cylinderSeparable contDiff_cylinderTimeWeight (contDiffOn_cylinderEscapeBarrier ρ)

theorem laplacian_cylinderEscapeFunction_nonneg {ρ : ℝ} (hρ : 0 < ρ)
    {x : CylinderSpace} (hx : x ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ 1) :
    0 ≤ Δ (cylinderEscapeFunction ρ) x := by
  rw [cylinderShell_eq_image hρ.le] at hx
  obtain ⟨⟨t, r, θ⟩, hp, rfl⟩ := hx
  have ht := hp.1
  have hr := hp.2.1
  change 0 ≤ Δ (cylinderSeparable cylinderTimeWeight (cylinderEscapeBarrier ρ))
    (cylinderPoint t r θ)
  rw [laplacian_cylinderSeparable contDiff_cylinderTimeWeight
    (contDiffOn_cylinderEscapeBarrier ρ) t r θ (hρ.trans_le hr.1),
    cylinderTimeWeight_second_deriv]
  have h := mul_nonneg (cylinderTimeWeight_nonneg ht)
    (sub_nonneg.mpr (cylinderEscapeBarrier_subsolution hρ hr.1 hr.2))
  nlinarith

/-- The genuine finite-cylinder escape estimate. Its outer-boundary input is
pointwise data, and its conclusion is obtained by the Laplacian maximum principle. -/
theorem cylinder_escape_lower {ρ m : ℝ} {f : CylinderSpace → ℝ} {U : Set CylinderSpace}
    (hρ : 0 < ρ) (hρ2 : 2 * ρ ≤ 1) (hm : 0 ≤ m)
    (hU : IsOpen U)
    (hKU : cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ 1 ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hn : ∀ x ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ 1, 0 ≤ f x)
    (hΔ : ∀ x ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ 1, Δ f x ≤ 0)
    (houter : ∀ x ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ 1,
      ‖(cylinderComplexEquiv x).2‖ = 1 → m ≤ f x) (θ : ℝ) :
    m * (Real.log 2 / (2 * (-Real.log ρ))) ≤ f (cylinderPoint 0 (2 * ρ) θ) := by
  let K := cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ 1
  let b := cylinderEscapeFunction ρ
  let c := m / cylinderEscapeBarrier ρ 1
  let v : CylinderSpace → ℝ := c • b - f
  have hρ1 : ρ < 1 := by linarith
  have hS := cylinderEscapeBarrier_outer_pos hρ hρ1
  have hc : 0 ≤ c := div_nonneg hm hS.le
  have hKA : K ⊆ cylinderAxisComplement := by
    intro x hx
    apply norm_pos_iff.mp
    exact hρ.trans_le hx.2.1
  have hKV : K ⊆ U ∩ cylinderAxisComplement := fun x hx => ⟨hKU hx, hKA hx⟩
  have hb : ContDiffOn ℝ ∞ b cylinderAxisComplement := contDiffOn_cylinderEscapeFunction ρ
  have hv : ContDiffOn ℝ ∞ v (U ∩ cylinderAxisComplement) :=
    ((contDiffOn_const.smul (hb.mono inter_subset_right)).sub (hf.mono inter_subset_left))
  have hbound : ∀ x ∈ K, v x ≤ 0 := by
    apply laplacian_maximum_on (isCompact_cylinderShell _ _ _ _)
      (hU.inter isOpen_cylinderAxisComplement) hKV hv
    · intro x hx
      have hxK : x ∈ K := interior_subset hx
      have hbx : ContDiffAt ℝ 2 b x :=
        ((hb x (hKA hxK)).contDiffAt
          (isOpen_cylinderAxisComplement.mem_nhds (hKA hxK))).of_le (by simp)
      have hfx : ContDiffAt ℝ 2 f x :=
        ((hf x (hKU hxK)).contDiffAt (hU.mem_nhds (hKU hxK))).of_le (by simp)
      have hcb : ContDiffAt ℝ 2 (c • b) x := contDiffAt_const.smul hbx
      change 0 ≤ Δ (c • b - f) x
      rw [hcb.laplacian_sub hfx, laplacian_smul c hbx]
      exact sub_nonneg.mpr (le_trans (hΔ x hxK)
        (mul_nonneg hc (laplacian_cylinderEscapeFunction_nonneg hρ hxK)))
    · intro x hx hi
      have hnonneg := hn x hx
      have hxTime : (cylinderComplexEquiv x).1 = x 0 := by
        simp only [cylinderComplexEquiv_apply]
      change c * cylinderSeparable cylinderTimeWeight (cylinderEscapeBarrier ρ) x - f x ≤ 0
      rcases cylinderShell_boundary hx hi with ht | ht | hr | hr
      · rw [hxTime] at ht
        simp only [cylinderSeparable, ht, cylinderTimeWeight_end.2, zero_mul, mul_zero]
        linarith
      · rw [hxTime] at ht
        simp only [cylinderSeparable, ht, cylinderTimeWeight_end.1, zero_mul, mul_zero]
        linarith
      · simp only [cylinderSeparable, hr, cylinderEscapeBarrier_inner, mul_zero]
        linarith
      · have hmf := houter x hx hr
        have hw : cylinderTimeWeight (x 0) ≤ 1 := Real.cos_le_one _
        have he : c * (cylinderTimeWeight (x 0) * cylinderEscapeBarrier ρ 1) =
            m * cylinderTimeWeight (x 0) := by
          dsimp [c]
          field_simp
        simp only [cylinderSeparable, hr, he]
        nlinarith [mul_le_mul_of_nonneg_left hw hm]
  have ht : (0 : ℝ) ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd := by
    dsimp [cylinderTimeEnd]
    constructor <;> nlinarith [Real.pi_pos]
  have hp : cylinderPoint 0 (2 * ρ) θ ∈ K :=
    cylinderPoint_mem_shell ht ⟨by linarith, hρ2⟩ (by positivity)
  have hpoint := hbound _ hp
  change c * cylinderSeparable cylinderTimeWeight (cylinderEscapeBarrier ρ)
    (cylinderPoint 0 (2 * ρ) θ) - f (cylinderPoint 0 (2 * ρ) θ) ≤ 0 at hpoint
  rw [cylinderSeparable_apply _ _ _ _ _ (by positivity)] at hpoint
  have hw0 : cylinderTimeWeight 0 = 1 := by simp [cylinderTimeWeight]
  rw [hw0, one_mul] at hpoint
  have hlo := mul_le_mul_of_nonneg_left (cylinderEscapeBarrier_ratio_lower hρ hρ1) hm
  dsimp [c] at hpoint
  nlinarith [show m * (cylinderEscapeBarrier ρ (2 * ρ) / cylinderEscapeBarrier ρ 1) =
    (m / cylinderEscapeBarrier ρ 1) * cylinderEscapeBarrier ρ (2 * ρ) by ring]

end OAI.Analysis.PDE.Concentration
