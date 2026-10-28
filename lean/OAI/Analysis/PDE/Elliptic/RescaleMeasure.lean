import OAI.Analysis.PDE.Elliptic.Scaling
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open Set _root_.MeasureTheory _root_.MeasureTheory.Measure
open scoped Pointwise
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem rescalePoint_inverse (z x : E) {r : ℝ} (hr : r ≠ 0) :
    rescalePoint z r (r⁻¹ • (x - z)) = x := by
  simp [rescalePoint, smul_smul, hr]

omit [FiniteDimensional ℝ E] in
theorem rescalePoint_surjective (z : E) {r : ℝ} (hr : r ≠ 0) :
    Function.Surjective (rescalePoint z r) :=
  fun x ↦ ⟨r⁻¹ • (x - z), rescalePoint_inverse z x hr⟩

omit [FiniteDimensional ℝ E] in
theorem dist_rescalePoint (z x : E) {r : ℝ} (hr : 0 ≤ r) :
    dist (rescalePoint z r x) z = r * ‖x‖ := by
  simp [dist_eq_norm, rescalePoint, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]

omit [FiniteDimensional ℝ E] in
theorem rescalePoint_image_ball (z : E) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    rescalePoint z r '' Metric.ball (0 : E) R = Metric.ball z (r * R) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.mem_ball, dist_rescalePoint z x hr.le]
    exact mul_lt_mul_of_pos_left (by simpa using hx) hr
  · intro hy
    obtain ⟨x, rfl⟩ := rescalePoint_surjective z hr.ne' y
    refine ⟨x, ?_, rfl⟩
    rw [Metric.mem_ball, dist_rescalePoint z x hr.le] at hy
    have hx : ‖x‖ < R := by nlinarith
    simpa using hx

variable [MeasurableSpace E] [BorelSpace E]

/-- Translation and positive spatial rescaling of an arbitrary set. -/
theorem measure_rescalePoint_image (μ : Measure E) [IsAddHaarMeasure μ]
    (z : E) {r : ℝ} (hr : 0 ≤ r) (S : Set E) :
    μ (rescalePoint z r '' S) = ENNReal.ofReal (r ^ Module.finrank ℝ E) * μ S := by
  have heq : rescalePoint z r '' S = (fun y : E ↦ -z + y) ⁻¹' (r • S) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change -z + (z + r • x) ∈ r • S
      simpa using smul_mem_smul_set hx
    · intro hy
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨x, hx, ?_⟩
      change z + r • x = y
      change r • x = -z + y at hxy
      rw [hxy]
      abel
  rw [heq, measure_preimage_add, addHaar_smul_of_nonneg μ hr]

theorem measureReal_rescalePoint_image (μ : Measure E) [IsAddHaarMeasure μ]
    (z : E) {r : ℝ} (hr : 0 ≤ r) (S : Set E) :
    μ.real (rescalePoint z r '' S) = r ^ Module.finrank ℝ E * μ.real S := by
  simp only [measureReal_def, measure_rescalePoint_image μ z hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr _)]

end OAI.Analysis.PDE.Elliptic
