import OAI.Analysis.Normed.Function.Sobolev.Reflection.Measure
import OAI.Analysis.Normed.Function.Sobolev.HalfspaceTest

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

variable {d N : ℕ}

def reflectionExtension (k : Fin d) (a c : Fin N → ℝ)
    (u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  {y | 0 < y k}.indicator u x +
    ∑ j, {y | y k < 0}.indicator (fun y ↦ c j * u (normalScale k (a j) y)) x

theorem reflectionExtension_eq (k : Fin d) (a c : Fin N → ℝ)
    (u : (Fin d → ℝ) → ℝ) {x : Fin d → ℝ} (hx : 0 < x k) :
    reflectionExtension k a c u x = u x := by
  simp [reflectionExtension, hx, not_lt.mpr hx.le]

theorem memLp_reflectionExtension (k : Fin d) (a c : Fin N → ℝ)
    (ha : ∀j, a j ≠ 0) {u : (Fin d → ℝ) → ℝ} {p : ENNReal}
    (hu : MemLp u p volume) : MemLp (reflectionExtension k a c u) p volume := by
  have hpos : MeasurableSet {x : Fin d → ℝ | 0 < x k} :=
    measurableSet_lt measurable_const (measurable_pi_apply k)
  have hneg : MeasurableSet {x : Fin d → ℝ | x k < 0} :=
    measurableSet_lt (measurable_pi_apply k) measurable_const
  exact (hu.indicator hpos).add (memLp_finsetSum _ (fun j _ ↦
    ((memLp_normalScale k (ha j) hu).const_mul (c j)).indicator hneg))

theorem integrable_reflectionExtension (k : Fin d) (a c : Fin N → ℝ)
    (ha : ∀j, a j ≠ 0) {u : (Fin d → ℝ) → ℝ}
    (hu : Integrable u) : Integrable (reflectionExtension k a c u) := by
  exact memLp_one_iff_integrable.mp (memLp_reflectionExtension k a c ha
    (memLp_one_iff_integrable.mpr hu))

theorem integrable_mul_compact_test {u φ : (Fin d → ℝ) → ℝ}
    (hu : Integrable u) (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable (fun x ↦ u x * φ x) := by
  obtain ⟨B,hB⟩ := hs.exists_bound_of_continuous hφ
  apply (hu.norm.mul_const B).mono' (hu.aestronglyMeasurable.mul hφ.aestronglyMeasurable)
  exact ae_of_all _ (fun x ↦ by
    change ‖u x * φ x‖ ≤ ‖u x‖ * B
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _))

theorem hasCompactSupport_normalScale (k : Fin d) {a : ℝ} (ha : a ≠ 0)
    {φ : (Fin d → ℝ) → ℝ} (hs : HasCompactSupport φ) :
    HasCompactSupport (fun x ↦ φ (normalScale k a x)) := by
  apply HasCompactSupport.intro (K := normalScale k a⁻¹ '' tsupport φ)
    (hs.isCompact.image (normalScale k a⁻¹).continuous)
  intro x hx
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  apply hx
  refine ⟨normalScale k a x, hm, ?_⟩
  simp [normalScale_comp, ha]

theorem integral_reflectionExtension_mul (k : Fin d) (a c : Fin N → ℝ)
    (ha : ∀j, a j < 0) {u φ : (Fin d → ℝ) → ℝ}
    (hu : Integrable u) (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    (∫x, reflectionExtension k a c u x * φ x) =
      (∫x in {x | 0 < x k}, u x * φ x) +
      ∑j, c j * |(a j)⁻¹| *
        (∫x in {x | 0 < x k}, u x * φ (normalScale k (a j)⁻¹ x)) := by
  have hpos : MeasurableSet {x : Fin d → ℝ | 0 < x k} :=
    measurableSet_lt measurable_const (measurable_pi_apply k)
  have hneg : MeasurableSet {x : Fin d → ℝ | x k < 0} :=
    measurableSet_lt (measurable_pi_apply k) measurable_const
  have hi0 := (integrable_mul_compact_test hu hφ hs).indicator hpos
  have hi (j : Fin N) := ((integrable_mul_compact_test
    (integrable_normalScale k (ha j).ne hu) hφ hs).const_mul (c j)).indicator hneg
  have heq (x : Fin d → ℝ) : reflectionExtension k a c u x * φ x =
      {x | 0 < x k}.indicator (fun x ↦ u x * φ x) x +
      ∑j, {x | x k < 0}.indicator (fun x ↦ c j * (u (normalScale k (a j) x) * φ x)) x := by
    simp only [reflectionExtension, add_mul, Finset.sum_mul]
    congr 1
    · by_cases hx : 0 < x k <;> simp [hx]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases hx : x k < 0 <;> simp [hx, mul_assoc]
  simp_rw [heq]
  rw [integral_add hi0 (MeasureTheory.integrable_finsetSum _ (fun j _ ↦ hi j)),
    MeasureTheory.integral_finsetSum _ (fun j _ ↦ hi j), integral_indicator hpos]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator hneg, integral_const_mul,
    setIntegral_normalScale_negative k (ha j)]
  ring

end OAI.Analysis.Normed.Function.Sobolev
