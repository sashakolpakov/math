import OAI.Analysis.PDE.Concentration.AngularAverage
import OAI.Analysis.PDE.Concentration.TimeWeight

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Laplacian InnerProductSpace
open scoped ContDiff

noncomputable def cylinderAverage (f : CylinderSpace → ℝ) (r : ℝ) : ℝ :=
  ∫ t in (-cylinderTimeEnd)..cylinderTimeEnd,
    cylinderTimeWeight t * cylinderAngularAverage f t r

theorem cylinderTimeEnd_pos : 0 < cylinderTimeEnd := by
  dsimp [cylinderTimeEnd]
  positivity

theorem contDiff_cylinderAverage {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (cylinderAverage f) := by
  have hA : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      cylinderTimeWeight p.2 * cylinderAngularAverage f p.2 p.1) :=
    (contDiff_cylinderTimeWeight.comp contDiff_snd).mul
      ((contDiff_cylinderAngularAverage hf).comp (contDiff_snd.prodMk contDiff_fst))
  exact contDiff_intervalAverage hA (by linarith [cylinderTimeEnd_pos])

theorem cylinderAngularAverage_nonneg {f : CylinderSpace → ℝ} {t r : ℝ}
    (hf : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), 0 ≤ f (cylinderPoint t r θ)) :
    0 ≤ cylinderAngularAverage f t r :=
  intervalIntegral.integral_nonneg (by positivity) hf

theorem cylinderAverage_nonneg {f : CylinderSpace → ℝ} {r : ℝ}
    (hf : ∀ t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd,
      ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), 0 ≤ f (cylinderPoint t r θ)) :
    0 ≤ cylinderAverage f r := by
  apply intervalIntegral.integral_nonneg (by linarith [cylinderTimeEnd_pos])
  intro t ht
  exact mul_nonneg (cylinderTimeWeight_nonneg ht) (cylinderAngularAverage_nonneg (hf t ht))

theorem cylinderAverage_first_deriv {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    deriv (cylinderAverage f) r =
      ∫ t in (-cylinderTimeEnd)..cylinderTimeEnd,
        cylinderTimeWeight t * deriv (fun s => cylinderAngularAverage f t s) r := by
  have hA : ContDiff ℝ ∞ (fun p : ℝ × ℝ => cylinderAngularAverage f p.2 p.1) :=
    (contDiff_cylinderAngularAverage hf).comp (contDiff_snd.prodMk contDiff_fst)
  exact deriv_weighted_intervalAverage hA contDiff_cylinderTimeWeight
    (by linarith [cylinderTimeEnd_pos]) r

theorem cylinderAverage_second_deriv {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    deriv (deriv (cylinderAverage f)) r =
      ∫ t in (-cylinderTimeEnd)..cylinderTimeEnd,
        cylinderTimeWeight t * deriv (deriv (fun s => cylinderAngularAverage f t s)) r := by
  have hA : ContDiff ℝ ∞ (fun p : ℝ × ℝ => cylinderAngularAverage f p.2 p.1) :=
    (contDiff_cylinderAngularAverage hf).comp (contDiff_snd.prodMk contDiff_fst)
  exact second_deriv_weighted_intervalAverage hA contDiff_cylinderTimeWeight
    (by linarith [cylinderTimeEnd_pos]) r

/-- The radial inequality is derived from the genuine three-dimensional
Laplacian and from nonnegative values on the two time faces. -/
theorem cylinderAverage_radialHelmholtz_nonpos {f : CylinderSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) {r : ℝ} (hr : r ≠ 0)
    (hΔ : ∀ t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd,
      ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), Δ f (cylinderPoint t r θ) ≤ 0)
    (hleft : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), 0 ≤ f (cylinderPoint (-cylinderTimeEnd) r θ))
    (hright : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), 0 ≤ f (cylinderPoint cylinderTimeEnd r θ)) :
    radialHelmholtz (cylinderAverage f) r ≤ 0 := by
  have hA := contDiff_cylinderAngularAverage hf
  have hswap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => cylinderAngularAverage f p.2 p.1) :=
    hA.comp (contDiff_snd.prodMk contDiff_fst)
  have hA1 : Continuous (fun t => deriv (fun s => cylinderAngularAverage f t s) r) :=
    continuous_firstPartial_slice hswap r
  have hA2 : Continuous (fun t => deriv (deriv (fun s => cylinderAngularAverage f t s)) r) :=
    continuous_secondPartial_slice hswap r
  have hAt : ContDiff ℝ ∞ (fun t => cylinderAngularAverage f t r) :=
    hA.comp (contDiff_id.prodMk contDiff_const)
  have hAt2 : Continuous (deriv (deriv (fun t => cylinderAngularAverage f t r))) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hAt).2).2.continuous
  have hpoint : ∀ t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd,
      deriv (deriv (fun s => cylinderAngularAverage f t s)) r +
        deriv (fun s => cylinderAngularAverage f t s) r / r ≤
          -deriv (deriv (fun s => cylinderAngularAverage f s r)) t := by
    intro t ht
    have hn := intervalIntegral.integral_nonneg (μ := volume) (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (fun θ hθ => neg_nonneg.mpr (hΔ t ht θ hθ))
    rw [intervalIntegral.integral_neg] at hn
    have he := cylinderAngularAverage_laplacian hf t r hr
    linarith
  have hweight := contDiff_cylinderTimeWeight.continuous
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (by linarith [cylinderTimeEnd_pos] : -cylinderTimeEnd ≤ cylinderTimeEnd)
    ((hweight.mul (hA2.add (hA1.div_const r))).intervalIntegrable _ _)
    ((hweight.mul hAt2.neg).intervalIntegrable _ _)
    (fun t ht => mul_le_mul_of_nonneg_left (hpoint t ht) (cylinderTimeWeight_nonneg ht))
  have heleft : (fun t => cylinderTimeWeight t *
      (deriv (deriv (fun s => cylinderAngularAverage f t s)) r +
        deriv (fun s => cylinderAngularAverage f t s) r / r)) =
      (fun t => cylinderTimeWeight t * deriv (deriv (fun s => cylinderAngularAverage f t s)) r +
        (cylinderTimeWeight t * deriv (fun s => cylinderAngularAverage f t s) r) / r) := by
    funext t; ring
  have heright : (fun t => cylinderTimeWeight t *
      -deriv (deriv (fun s => cylinderAngularAverage f s r)) t) =
      (fun t => -(cylinderTimeWeight t * deriv (deriv (fun s => cylinderAngularAverage f s r)) t)) := by
    funext t; ring
  simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply] at hmono
  rw [heleft, heright, intervalIntegral.integral_add
    (f := fun t => cylinderTimeWeight t * deriv (deriv (fun s => cylinderAngularAverage f t s)) r)
    (g := fun t => (cylinderTimeWeight t * deriv (fun s => cylinderAngularAverage f t s) r) / r)
    ((hweight.mul hA2).intervalIntegrable _ _)
    (((hweight.mul hA1).div_const r).intervalIntegrable _ _),
    intervalIntegral.integral_div, intervalIntegral.integral_neg,
    ← cylinderAverage_second_deriv hf, ← cylinderAverage_first_deriv hf] at hmono
  have htime := cylinderTimeWeight_second_deriv_lower (hAt.of_le (by simp))
    (cylinderAngularAverage_nonneg hleft) (cylinderAngularAverage_nonneg hright)
  change -(cylinderAverage f r) / 100 ≤ _ at htime
  dsimp [radialHelmholtz]
  linarith

theorem cylinderAverage_logarithmic_lower {f : CylinderSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hnonneg : ∀ r ∈ Icc a 3, ∀ t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd,
      ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), 0 ≤ f (cylinderPoint t r θ))
    (hΔ : ∀ r ∈ Ioo a 3, ∀ t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd,
      ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), Δ f (cylinderPoint t r θ) ≤ 0) :
    cylinderAverage f a * (Real.log 3 / (4 * (Real.log 3 - Real.log a))) ≤
      cylinderAverage f 1 := by
  have ha3 : a ≤ 3 := by linarith
  have htime : -cylinderTimeEnd ≤ cylinderTimeEnd := by linarith [cylinderTimeEnd_pos]
  apply radialHelmholtz_unit_lower ha ha1 (contDiff_cylinderAverage hf).continuous.continuousOn
    ((contDiff_cylinderAverage hf).of_le (by simp)).contDiffOn
  · intro r hr
    exact cylinderAverage_radialHelmholtz_nonpos hf (ha.trans hr.1).ne' (hΔ r hr)
      (hnonneg r (Ioo_subset_Icc_self hr) _ ⟨le_rfl, htime⟩)
      (hnonneg r (Ioo_subset_Icc_self hr) _ ⟨htime, le_rfl⟩)
  · exact cylinderAverage_nonneg (hnonneg a ⟨le_rfl, ha3⟩)
  · exact cylinderAverage_nonneg (hnonneg 3 ⟨ha3, le_rfl⟩)

theorem cylinderAverage_congr {f g : CylinderSpace → ℝ} {r : ℝ}
    (he : ∀ t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd,
      ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), f (cylinderPoint t r θ) = g (cylinderPoint t r θ)) :
    cylinderAverage f r = cylinderAverage g r := by
  unfold cylinderAverage cylinderAngularAverage
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by linarith [cylinderTimeEnd_pos] : -cylinderTimeEnd ≤ cylinderTimeEnd)] at ht
  dsimp only
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] at hθ
  exact he t ht θ hθ

end OAI.Analysis.PDE.Concentration
