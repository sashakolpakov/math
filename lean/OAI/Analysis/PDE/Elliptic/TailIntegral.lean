import OAI.Analysis.PDE.Elliptic.TailPointwise
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open Set _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {X : Type*} [MeasurableSpace X]

theorem lintegral_rpow_le_geometric_tail (mu : Measure X) {u : X → ℝ}
    (hu : Measurable u) {M theta p : ℝ} (hM : 1 < M) (hp : 0 ≤ p)
    (htail : ∀ k : ℕ, mu {x | M ^ k < u x} ≤ ENNReal.ofReal theta ^ k * mu univ) :
    ∫⁻ x, ENNReal.ofReal (u x) ^ p ∂mu ≤
      (1 + (ENNReal.ofReal M ^ p) *
        ∑' k : ℕ, ((ENNReal.ofReal M ^ p) * ENNReal.ofReal theta) ^ k) * mu univ := by
  let a := ENNReal.ofReal M ^ p
  let f : ℕ → X → ℝ≥0∞ := fun k x ↦ if M ^ k < u x then a ^ (k + 1) else 0
  have hf (k : ℕ) : Measurable (f k) := by
    change Measurable ({x | M ^ k < u x}.indicator (fun _ ↦ a ^ (k + 1)))
    exact measurable_const.indicator (measurableSet_lt measurable_const hu)
  have hi (k : ℕ) : ∫⁻ x, f k x ∂mu = a ^ (k + 1) * mu {x | M ^ k < u x} := by
    change (∫⁻ x, {x | M ^ k < u x}.indicator (fun _ ↦ a ^ (k + 1)) x ∂mu) = _
    rw [lintegral_indicator (measurableSet_lt measurable_const hu), lintegral_const]
    simp only [Measure.restrict_apply_univ]
  calc
    ∫⁻ x, ENNReal.ofReal (u x) ^ p ∂mu ≤ ∫⁻ x, 1 + ∑' k : ℕ, f k x ∂mu :=
      lintegral_mono (fun x ↦ rpow_le_geometric_indicators hM hp (u x))
    _ = mu univ + ∑' k : ℕ, a ^ (k + 1) * mu {x | M ^ k < u x} := by
      rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
        lintegral_tsum (fun k ↦ (hf k).aemeasurable)]
      congr 1
      exact tsum_congr hi
    _ ≤ mu univ + ∑' k : ℕ, a ^ (k + 1) * (ENNReal.ofReal theta ^ k * mu univ) := by
      exact add_le_add le_rfl
        (ENNReal.tsum_le_tsum (fun k ↦ mul_le_mul_of_nonneg_left (htail k) zero_le))
    _ = (1 + a * ∑' k : ℕ, (a * ENNReal.ofReal theta) ^ k) * mu univ := by
      have he (k : ℕ) : a ^ (k + 1) * (ENNReal.ofReal theta ^ k * mu univ) =
          (a * (a * ENNReal.ofReal theta) ^ k) * mu univ := by
        rw [pow_succ, mul_pow]
        ac_rfl
      simp_rw [he]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, add_mul, one_mul]

end OAI.Analysis.PDE.Elliptic
