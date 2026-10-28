import OAI.Analysis.PDE.Elliptic.GrowthFraction
import OAI.Analysis.PDE.Elliptic.RescaleMeasure

open Set _root_.MeasureTheory _root_.MeasureTheory.Measure
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The growth estimate on arbitrary balls, with constants independent
of the center, radius, amplitude, coefficients, and supersolution. -/
theorem uniform_sublevel_growth_balls_large (μ : Measure E) [IsAddHaarMeasure μ]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) {R : ℝ} (hR : 1 ≤ R) :
    ∃ M delta : ℝ, 1 < M ∧ 0 < delta ∧ delta < 1 ∧
      ∀ (z : E) (r t : ℝ), 0 < r → 0 < t →
      ∀ (A : E → E →L[ℝ] E) (u : E → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ Metric.closedBall z (2 * R * r), 0 ≤ u x) →
      (∀ x ∈ Metric.closedBall z (2 * R * r), ∀ v : E,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ Metric.closedBall z (2 * R * r), ∀ v : E,
        inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ Metric.ball z (2 * R * r), ellipticTrace A u x ≤ 0) →
      ∀ x₀ ∈ Metric.closedBall z (R * r), u x₀ ≤ t →
        delta * μ.real (Metric.ball z r) ≤
          μ.real {x : E | dist x z < r ∧ u x ≤ t * M} := by
  obtain ⟨M, delta, hM, hd, hd1, hg⟩ := uniform_sublevel_growth_fraction_large μ hlam hL hR
  have hRpos : 0 < R := by linarith
  refine ⟨M, delta, hM, hd, hd1, ?_⟩
  intro z r t hr ht A u hu hnonneg hlo hhi hLu x₀ hx₀ hux₀
  let v : E → ℝ := fun y ↦ t⁻¹ • u (rescalePoint z r y)
  let B : E → E →L[ℝ] E := fun y ↦ A (rescalePoint z r y)
  have hcomp : ContDiff ℝ 2 (fun y ↦ u (rescalePoint z r y)) :=
    hu.comp ((rescalePoint_contDiff z r).of_le (by simp))
  have hv : ContDiff ℝ 2 v := hcomp.const_smul t⁻¹
  have hmap (y : E) (hy : y ∈ Metric.closedBall (0 : E) (2 * R)) :
      rescalePoint z r y ∈ Metric.closedBall z (2 * R * r) := by
    rw [Metric.mem_closedBall, dist_rescalePoint z y hr.le]
    have hn : ‖y‖ ≤ 2 * R := by simpa using hy
    nlinarith
  have hmap' (y : E) (hy : y ∈ interior (Metric.closedBall (0 : E) (2 * R))) :
      rescalePoint z r y ∈ Metric.ball z (2 * R * r) := by
    rw [interior_closedBall _ (by positivity : 2 * R ≠ 0)] at hy
    rw [Metric.mem_ball, dist_rescalePoint z y hr.le]
    have hn : ‖y‖ < 2 * R := by simpa using hy
    nlinarith
  obtain ⟨y₀, hy₀⟩ := rescalePoint_surjective z hr.ne' x₀
  have hy₀ball : y₀ ∈ Metric.closedBall (0 : E) R := by
    have hdist := dist_rescalePoint z y₀ hr.le
    rw [hy₀] at hdist
    have hnorm : ‖y₀‖ ≤ R := by
      have hh : dist x₀ z ≤ R * r := hx₀
      nlinarith
    simpa using hnorm
  have hv₀ : v y₀ ≤ 1 := by
    dsimp [v]
    rw [hy₀]
    calc
      t⁻¹ * u x₀ ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left hux₀ (inv_nonneg.mpr ht.le)
      _ = 1 := inv_mul_cancel₀ ht.ne'
  have hest := hg B v hv
    (fun y hy ↦ mul_nonneg (inv_nonneg.mpr ht.le) (hnonneg _ (hmap y hy)))
    (fun y hy w ↦ hlo _ (hmap y hy) w)
    (fun y hy w ↦ hhi _ (hmap y hy) w)
    (fun y hy ↦ by
      change ellipticTrace B (fun y ↦ t⁻¹ • u (rescalePoint z r y)) y ≤ 0
      rw [ellipticTrace_smul B hcomp]
      change t⁻¹ * ellipticTrace (fun y ↦ A (rescalePoint z r y))
        (fun y ↦ u (rescalePoint z r y)) y ≤ 0
      rw [ellipticTrace_rescalePoint A hu]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) (hLu _ (hmap' y hy))))
    y₀ hy₀ball hv₀
  let S : Set E := {y | ‖y‖ < 1 ∧ v y ≤ M}
  have himage : rescalePoint z r '' S = {x : E | dist x z < r ∧ u x ≤ t * M} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [dist_rescalePoint z y hr.le]
        nlinarith [hy.1]
      · have hh : u (rescalePoint z r y) / t ≤ M := by
          simpa only [v, smul_eq_mul, div_eq_mul_inv, mul_comm] using hy.2
        have hh' := (div_le_iff₀ ht).mp hh
        simpa only [mul_comm] using hh'
    · intro hx
      obtain ⟨y, rfl⟩ := rescalePoint_surjective z hr.ne' x
      change dist (rescalePoint z r y) z < r ∧ u (rescalePoint z r y) ≤ t * M at hx
      refine ⟨y, ⟨?_, ?_⟩, rfl⟩
      · rw [dist_rescalePoint z y hr.le] at hx
        nlinarith [hx.1]
      · have hh : u (rescalePoint z r y) / t ≤ M :=
          (div_le_iff₀ ht).mpr (by simpa only [mul_comm] using hx.2)
        simpa only [v, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh
  calc
    delta * μ.real (Metric.ball z r) =
        r ^ Module.finrank ℝ E * (delta * μ.real (Metric.ball (0 : E) 1)) := by
      have hh := measureReal_rescalePoint_image μ z hr.le (Metric.ball (0 : E) 1)
      rw [rescalePoint_image_ball z hr, mul_one] at hh
      rw [hh]
      ring
    _ ≤ r ^ Module.finrank ℝ E * μ.real S :=
      mul_le_mul_of_nonneg_left hest (pow_nonneg hr.le _)
    _ = μ.real {x : E | dist x z < r ∧ u x ≤ t * M} := by
      rw [← measureReal_rescalePoint_image μ z hr.le S, himage]

theorem uniform_sublevel_growth_balls (μ : Measure E) [IsAddHaarMeasure μ]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ M delta : ℝ, 1 < M ∧ 0 < delta ∧ delta < 1 ∧
      ∀ (z : E) (r t : ℝ), 0 < r → 0 < t →
      ∀ (A : E → E →L[ℝ] E) (u : E → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ Metric.closedBall z (2 * r), 0 ≤ u x) →
      (∀ x ∈ Metric.closedBall z (2 * r), ∀ v : E,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ Metric.closedBall z (2 * r), ∀ v : E,
        inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ Metric.ball z (2 * r), ellipticTrace A u x ≤ 0) →
      ∀ x₀ ∈ Metric.closedBall z r, u x₀ ≤ t →
        delta * μ.real (Metric.ball z r) ≤
          μ.real {x : E | dist x z < r ∧ u x ≤ t * M} := by
  simpa using uniform_sublevel_growth_balls_large μ hlam hL (R := 1) le_rfl

end OAI.Analysis.PDE.Elliptic
