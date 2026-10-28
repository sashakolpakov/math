import OAI.Analysis.PDE.Green.GreenReal

/-! Zero extension and genuine boundary integration by parts.
The null-boundary hypothesis is the usual measure-theoretic regularity condition. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory Measure
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Zero extension preserves a Lipschitz constant when the boundary value is zero. -/
theorem lipschitz_indicator_of_zero_frontier {S : Set E} {u : E → ℝ} {C : ℝ≥0}
    (hu : LipschitzWith C u) (hz : ∀ x ∈ frontier S, u x = 0) :
    LipschitzWith C (S.indicator u) := by
  have hcross (x y : E) (hx : x ∈ S) (hy : y ∉ S) :
      dist (u x) 0 ≤ (C : ℝ) * dist x y := by
    have hS : S ≠ univ := by intro he; exact hy (he ▸ mem_univ y)
    obtain ⟨z,hzS,hzd⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hS
    calc
      dist (u x) 0 = dist (u x) (u z) := by rw [hz z hzS]
      _ ≤ (C : ℝ) * dist x z := hu.dist_le_mul x z
      _ = (C : ℝ) * Metric.infDist x Sᶜ := by rw [hzd]
      _ ≤ (C : ℝ) * dist x y := mul_le_mul_of_nonneg_left
        (Metric.infDist_le_dist_of_mem hy) C.coe_nonneg
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simpa only [indicator_of_mem hx, indicator_of_mem hy] using hu.dist_le_mul x y
  · simpa only [indicator_of_mem hx, indicator_of_notMem hy] using hcross x y hx hy
  · simpa only [indicator_of_notMem hx, indicator_of_mem hy, dist_comm] using hcross y x hy hx
  · simp only [indicator_of_notMem hx, indicator_of_notMem hy, dist_self]
    positivity

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem hasCompactSupport_indicator {S : Set E} {u : E → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (S.indicator u) := by
  apply hu.mono'
  intro x hx
  by_contra hn
  have hz : u x = 0 := image_eq_zero_of_notMem_tsupport hn
  have hzero : S.indicator u x = 0 := by by_cases h : x ∈ S <;> simp [h, hz]
  exact hx hzero

omit [FiniteDimensional ℝ E] in
theorem lineDeriv_indicator_off_frontier {S : Set E} (hS : IsOpen S)
    {u : E → ℝ} (hu : Differentiable ℝ u) {x : E} (hx : x ∉ frontier S) (d : E) :
    lineDeriv ℝ (S.indicator u) x d = S.indicator (fun y ↦ fderiv ℝ u y d) x := by
  by_cases hm : x ∈ S
  · have he : S.indicator u =ᶠ[𝓝 x] u := by
      filter_upwards [hS.mem_nhds hm] with y hy
      exact indicator_of_mem hy u
    rw [he.lineDeriv_eq, (hu x).lineDeriv_eq_fderiv, indicator_of_mem hm]
  · have hc : x ∈ (closure S)ᶜ := by
      intro hh
      apply hx
      exact ⟨hh, by simpa only [hS.interior_eq] using hm⟩
    have he : S.indicator u =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy
      exact indicator_of_notMem (fun hh ↦ hy (subset_closure hh)) u
    rw [he.lineDeriv_eq, indicator_of_notMem hm]
    exact (hasFDerivAt_const (0 : ℝ) x).hasLineDerivAt d |>.lineDeriv

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsAddHaarMeasure μ]

omit [BorelSpace E] [μ.IsAddHaarMeasure] [FiniteDimensional ℝ E] in
theorem ae_lineDeriv_indicator {S : Set E} (hS : IsOpen S)
    (hnull : μ (frontier S) = 0) {u : E → ℝ} (hu : Differentiable ℝ u) (d : E) :
    (fun x ↦ lineDeriv ℝ (S.indicator u) x d) =ᵐ[μ]
      S.indicator (fun x ↦ fderiv ℝ u x d) := by
  have ha : ∀ᵐ x ∂μ, x ∉ frontier S := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  filter_upwards [ha] with x hx
  exact lineDeriv_indicator_off_frontier hS hu hx d

/-- Zero Dirichlet boundary values remove the boundary term in integration by
parts. Only the test function must vanish on the boundary. -/
theorem integral_directional_by_parts_zero_boundary {S : Set E} (hS : IsOpen S)
    (hnull : μ (frontier S) = 0) {u v : E → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hsu : HasCompactSupport u) (hsv : HasCompactSupport v)
    (hz : ∀ x ∈ frontier S, u x = 0) (d : E) :
    (∫ x in S, u x * fderiv ℝ v x d ∂μ) =
      -(∫ x in S, fderiv ℝ u x d * v x ∂μ) := by
  obtain ⟨C,hul⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsu hu (by norm_num)
  obtain ⟨D,hvl⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsv hv (by norm_num)
  have h := LipschitzWith.integral_lineDeriv_mul_eq (μ := μ) hvl
    (lipschitz_indicator_of_zero_frontier hul hz)
    (hasCompactSupport_indicator hsu) d
  have ha := ae_lineDeriv_indicator (μ := μ) hS hnull (hu.differentiable (by norm_num)) (-d)
  have hr : (∫ x, lineDeriv ℝ (S.indicator u) x (-d) * v x ∂μ) =
      -(∫ x in S, fderiv ℝ u x d * v x ∂μ) := by
    calc
      _ = ∫ x, S.indicator (fun y ↦ fderiv ℝ u y (-d)) x * v x ∂μ :=
        integral_congr_ae (ha.fun_mul (EventuallyEq.refl _ _))
      _ = ∫ x, S.indicator (fun y ↦ -(fderiv ℝ u y d * v y)) x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x ↦ by by_cases hx : x ∈ S <;> simp [hx])
      _ = _ := by rw [integral_indicator hS.measurableSet, integral_neg]
  rw [hr] at h
  convert h using 1
  rw [← integral_indicator hS.measurableSet]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    change S.indicator (fun y ↦ u y * fderiv ℝ v y d) x =
      lineDeriv ℝ v x d * S.indicator u x
    rw [(hv.differentiable (by norm_num) x).lineDeriv_eq_fderiv]
    by_cases hx : x ∈ S <;> simp [hx, mul_comm])

/-- The divergence formula on a domain, with actual zero boundary data. -/
theorem integral_divergence_by_parts_zero_boundary {I : Type*} [Fintype I]
    {S : Set E} (hS : IsOpen S) (hnull : μ (frontier S) = 0)
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (hz : ∀ x ∈ frontier S, u x = 0)
    (d : I → E) (F : I → E → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    (hsF : ∀ i, HasCompactSupport (F i)) :
    (∫ x in S, u x * (∑ i, fderiv ℝ (F i) x (d i)) ∂μ) =
      -(∫ x in S, ∑ i, fderiv ℝ u x (d i) * F i x ∂μ) := by
  have hleft (i : I) : Integrable (fun x ↦ u x * fderiv ℝ (F i) x (d i)) (μ.restrict S) :=
    ((hu.continuous.mul (continuous_directional (hF i) (d i))).integrable_of_hasCompactSupport
      hs.mul_right).restrict
  have hright (i : I) : Integrable (fun x ↦ fderiv ℝ u x (d i) * F i x) (μ.restrict S) :=
    (((continuous_directional hu (d i)).mul (hF i).continuous).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ (d i)).mul_right).restrict
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hleft i), integral_finsetSum _ (fun i _ ↦ hright i)]
  simp_rw [integral_directional_by_parts_zero_boundary hS hnull hu (hF _) hs (hsF _) hz]
  exact Finset.sum_neg_distrib _

end OAI.Analysis.PDE.Green
