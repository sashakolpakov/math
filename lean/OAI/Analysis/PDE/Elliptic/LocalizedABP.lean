import OAI.Analysis.PDE.Elliptic.NegativeABP

open Set _root_.MeasureTheory _root_.MeasureTheory.Measure
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- When the positive forcing is bounded and supported in `S`, ABP gives
a quantitative lower bound on the measure of negative contacts in `S`. -/
theorem abp_localized_forcing
    (μ : Measure E) [IsAddHaarMeasure μ] {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x₀ : E} (hx₀ : x₀ ∈ K)
    (hnegative : f x₀ < 0) (hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    {R : ℝ} (hR : 0 < R) (hradius : ∀ x ∈ K, ‖x - x₀‖ ≤ R)
    (A : E → E →L[ℝ] E) {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ x ∈ negativeContactSet K f, ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    {S : Set E} (hS : MeasurableSet S) {B : ℝ} (hB : 0 ≤ B)
    (hinside : ∀ x ∈ negativeContactSet K f, x ∈ S → ellipticTrace A f x ≤ B)
    (houtside : ∀ x ∈ negativeContactSet K f, x ∉ S → ellipticTrace A f x ≤ 0) :
    μ (Metric.ball (0 : E) (-f x₀ / R)) ≤
      ENNReal.ofReal (B / lam) ^ Module.finrank ℝ E * μ (negativeContactSet K f ∩ S) := by
  classical
  let g : E → ℝ := fun x ↦ if x ∈ S then B else 0
  have hg : ∀ x ∈ negativeContactSet K f, ellipticTrace A f x ≤ g x := by
    intro x hx
    by_cases hs : x ∈ S
    · simpa only [g, ite_eq_left hs] using hinside x hx hs
    · simpa only [g, ite_eq_right hs] using houtside x hx hs
  have h := abp_negative_contact_bound μ hK hf hx₀ hnegative hboundary hR hradius A hlam hA g hg
  have hn : Module.finrank ℝ E ≠ 0 := (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have heq : (fun x ↦ ENNReal.ofReal ((max (g x) 0 / lam) ^ Module.finrank ℝ E)) =
      S.indicator (fun _ ↦ ENNReal.ofReal (B / lam) ^ Module.finrank ℝ E) := by
    funext x
    by_cases hs : x ∈ S
    · simp only [g, ite_eq_left hs, max_eq_left hB, indicator_of_mem hs,
        ENNReal.ofReal_pow (div_nonneg hB hlam.le)]
    · simp only [g, ite_eq_right hs, max_self, zero_div, zero_pow hn,
        ENNReal.ofReal_zero, indicator_of_notMem hs]
  rw [heq, lintegral_indicator hS, lintegral_const] at h
  simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Measure.restrict_apply hS, inter_comm S] using h

end OAI.Analysis.PDE.Elliptic
