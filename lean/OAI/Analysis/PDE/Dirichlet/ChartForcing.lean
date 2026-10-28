import OAI.Analysis.PDE.Elliptic.DirichletChartHolderFields

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

theorem continuous_of_positive_holder_bound
    {X : Type*} [PseudoMetricSpace X] {g : X → ℝ} {α B : ℝ}
    (hα : 0 < α) (hh : ∀ x y, |g x - g y| ≤ B * dist x y ^ α) : Continuous g := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : Continuous (fun y : X ↦ B * dist y x ^ α) :=
    continuous_const.mul ((continuous_id.dist continuous_const).rpow_const (fun _ ↦ Or.inr hα.le))
  have ht : Tendsto (fun y : X ↦ B * dist y x ^ α) (𝓝 x) (𝓝 0) := by
    simpa only [dist_self, Real.zero_rpow hα.ne', mul_zero] using hc.tendsto x
  filter_upwards [ht (gt_mem_nhds hε)] with y hy
  have hd : dist (g y) (g x) ≤ B * dist y x ^ α := by
    simpa only [Real.dist_eq] using hh y x
  exact hd.trans_lt hy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A fixed C¹ chart has a genuine Lipschitz constant on a compact convex
patch, obtained from the maximum of the norm of its derivative. -/
theorem exists_compact_convex_chart_bound
    (G : E → E) (hG : ContDiff ℝ 1 G) {S : Set E}
    (hS : IsCompact S) (hSc : Convex ℝ S) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ S, ∀ y ∈ S, dist (G x) (G y) ≤ L * dist x y := by
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn
    (hG.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro x hx y hy
  have hder z (hz : z ∈ S) : ‖fderiv ℝ G z‖ ≤ |M| + 1 :=
    (hM z hz).trans ((le_abs_self M).trans (by linarith))
  simpa only [dist_eq_norm] using
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hG.differentiable (by norm_num) z) hder hSc hy hx

/-- Raw forcing needs bounds only on the physical set K. The global Hölder
extension of its pullback is constructed, and its constant is chosen before
K, the forcing, and its norm bound. -/
theorem exists_chart_raw_forcing_extension
    (G : E → E) (hG : ContDiff ℝ 1 G) {S : Set E}
    (hne : S.Nonempty) (hS : IsCompact S) (hSc : Convex ℝ S)
    {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Set E, MapsTo G S K →
      ∀ B : ℝ, 0 ≤ B → ∀ g : E → ℝ,
      (∀ x ∈ K, |g x| ≤ B) →
      (∀ x ∈ K, ∀ y ∈ K, |g x - g y| ≤ B * dist x y ^ α) →
      ∃ F : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α,
        (∀ x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value F x = g (G x)) ∧ ‖F‖ ≤ C * B := by
  obtain ⟨L, hL, hLb⟩ := exists_compact_convex_chart_bound G hG hS hSc
  let C := 1 + L ^ α
  have hC1 : 1 ≤ C := by
    dsimp [C]
    have := Real.rpow_nonneg hL.le α
    linarith
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC1, ?_⟩
  intro K hGK B hB g hgn hgh
  let f : S → ℝ := fun x ↦ g (G x)
  have hfn (x : S) : ‖f x‖ ≤ C * B := by
    change |g (G x)| ≤ C * B
    exact (hgn (G x) (hGK x.property)).trans (by nlinarith)
  have hfh (x y : S) : |f x - f y| ≤ (C * B) * dist x y ^ α := by
    calc
      |f x - f y| ≤ B * dist (G x) (G y) ^ α := hgh _ (hGK x.property) _ (hGK y.property)
      _ ≤ B * (L * dist (x : E) (y : E)) ^ α :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow dist_nonneg (hLb x x.property y y.property) hα.le) hB
      _ = (L ^ α * B) * dist x y ^ α := by
        rw [Real.mul_rpow hL.le dist_nonneg]
        simp only [Subtype.dist_eq]
        ring
      _ ≤ (C * B) * dist x y ^ α := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg α)
        exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hB
  obtain ⟨F, hF, hFn⟩ := OAI.Analysis.PDE.Elliptic.exists_convex_holder_extension_of_bounds
    hne hS.isComplete hSc hα.le (mul_nonneg (zero_le_one.trans hC1) hB)
    f (continuous_of_positive_holder_bound hα hfh) hfn
    (fun x y ↦ by simpa only [Real.norm_eq_abs] using hfh x y)
  exact ⟨F, fun x hx ↦ hF ⟨x, hx⟩, hFn⟩

/-- Hölder data on the physical domain admit a global Hölder forcing in a
fixed coordinate chart, with operator bound independent of the data. -/
theorem exists_chart_forcing_extension
    (G : E → E) (hG : ContDiff ℝ 1 G) {S : Set E}
    (hne : S.Nonempty) (hS : IsCompact S) (hSc : Convex ℝ S)
    {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Set E, ∀ hGK : MapsTo G S K,
      ∀ f : OAI.Analysis.Normed.Function.Holder.HolderMap K ℝ α, ∃ F : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α,
        (∀ x (hx : x ∈ S), OAI.Analysis.Normed.Function.Holder.HolderMap.value F x = OAI.Analysis.Normed.Function.Holder.HolderMap.value f ⟨G x, hGK hx⟩) ∧
          ‖F‖ ≤ C * ‖f‖ := by
  classical
  obtain ⟨C, hC, hCe⟩ := exists_chart_raw_forcing_extension G hG hne hS hSc hα
  refine ⟨C, hC, ?_⟩
  intro K hGK f
  let g : E → ℝ := fun x ↦ if hx : x ∈ K then OAI.Analysis.Normed.Function.Holder.HolderMap.value f ⟨x, hx⟩ else 0
  have hgn x (hx : x ∈ K) : |g x| ≤ ‖f‖ := by
    simpa only [g, dite_eq_left hx, Real.norm_eq_abs] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le f ⟨x, hx⟩
  have hgh x (hx : x ∈ K) y (hy : y ∈ K) : |g x - g y| ≤ ‖f‖ * dist x y ^ α := by
    simpa only [g, dite_eq_left hx, dite_eq_left hy, Real.norm_eq_abs, Subtype.dist_eq] using
      OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨F, hF, hFn⟩ := hCe K hGK ‖f‖ (norm_nonneg f) g hgn hgh
  refine ⟨F, ?_, hFn⟩
  intro x hx
  rw [hF x hx]
  exact dite_eq_left (hGK hx)

end OAI.Analysis.PDE.Dirichlet
