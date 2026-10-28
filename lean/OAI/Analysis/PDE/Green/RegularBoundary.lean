import OAI.Analysis.PDE.Green.TangentialFlux
import OAI.Analysis.PDE.Dirichlet.LevelSet

/-! Regular level sets give the normal quotient bound needed by cutoff Green. -/

noncomputable section
open Set Filter _root_.MeasureTheory Measure
open scoped Topology NNReal

namespace OAI.Analysis.PDE.Green

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A function vanishing on a regular level set is bounded locally by the defining
function. The chart and its Lipschitz bound come from the inverse function theorem. -/
theorem implicit_zero_local_bound
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (φ : ImplicitFunctionData ℝ E ℝ G) {q : E → ℝ} {q' : E →L[ℝ] ℝ}
    (hq : HasStrictFDerivAt q q' φ.pt)
    (hz : ∀ᶠ y in 𝓝 φ.pt, φ.leftFun y = φ.leftFun φ.pt → q y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 φ.pt,
      ‖q y‖ ≤ C * ‖φ.leftFun y - φ.leftFun φ.pt‖ := by
  have hG := φ.hasStrictFDerivAt.to_localInverse
  rw [HasStrictFDerivAt.localInverse_def] at hG
  change HasStrictFDerivAt φ.implicitFunction.uncurry _ _ at hG
  obtain ⟨K, U, hU, hKU⟩ := hG.exists_lipschitzOnWith
  obtain ⟨L, V, hV, hLV⟩ := hq.exists_lipschitzOnWith
  let R : E → E := fun y => φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun y)
  have hbase : φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun φ.pt) = φ.pt :=
    φ.implicitFunction_apply_image.self_of_nhds
  have hfix : Tendsto (fun y => (φ.leftFun φ.pt, φ.rightFun y)) (𝓝 φ.pt)
      (𝓝 (φ.prodFun φ.pt)) :=
    continuousAt_const.prodMk φ.hasStrictFDerivAt_rightFun.continuousAt
  have hR : Tendsto R (𝓝 φ.pt) (𝓝 φ.pt) := by
    simpa only [R, Function.comp_def, Function.uncurry_apply_pair, ImplicitFunctionData.prodFun_apply, hbase]
      using hG.continuousAt.tendsto.comp hfix
  refine ⟨(L : ℝ) * K, by positivity, ?_⟩
  filter_upwards [hV, hR hV, φ.hasStrictFDerivAt.continuousAt.tendsto hU,
    hfix hU, φ.implicitFunction_apply_image,
    φ.leftFun_implicitFunction_eq_leftFun, hR hz] with y hy hRy hUy hUfy hIy hrY hzY
  have hqR : q (R y) = 0 := hzY hrY
  have hdist : dist y (R y) ≤ (K : ℝ) * ‖φ.leftFun y - φ.leftFun φ.pt‖ := by
    calc
      dist y (R y) = dist (φ.implicitFunction.uncurry (φ.prodFun y))
          (φ.implicitFunction.uncurry (φ.leftFun φ.pt, φ.rightFun y)) := by
            simpa only [Function.uncurry_apply_pair, ImplicitFunctionData.prodFun_apply, R] using
              congrArg (fun z => dist z (R y)) hIy.symm
      _ ≤ (K : ℝ) * dist (φ.prodFun y) (φ.leftFun φ.pt, φ.rightFun y) :=
        hKU.dist_le_mul _ hUy _ hUfy
      _ = (K : ℝ) * ‖φ.leftFun y - φ.leftFun φ.pt‖ := by
        simp [ImplicitFunctionData.prodFun_apply, dist_eq_norm]
  calc
    ‖q y‖ = dist (q y) (q (R y)) := by rw [hqR, dist_zero_right]
    _ ≤ (L : ℝ) * dist y (R y) := hLV.dist_le_mul _ hy _ hRy
    _ ≤ (L : ℝ) * ((K : ℝ) * ‖φ.leftFun y - φ.leftFun φ.pt‖) :=
      mul_le_mul_of_nonneg_left hdist L.coe_nonneg
    _ = _ := by ring

/-- The local quotient estimate expressed without chart data. -/
theorem regular_zero_local_bound {r q : E → ℝ} {x : E}
    (hr : ContDiff ℝ 1 r) (hq : ContDiff ℝ 1 q)
    (hrne : fderiv ℝ r x ≠ 0) (hrx : r x = 0)
    (hz : ∀ y, r y = 0 → q y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, ‖q y‖ ≤ C * ‖r y‖ := by
  let r' := fderiv ℝ r x
  let hsurj := OAI.Analysis.PDE.Dirichlet.real_linear_form_range_top r' hrne
  let φ := (hr.hasStrictFDerivAt (by norm_num) (x := x)).implicitFunctionDataOfComplemented
    r r' hsurj r'.ker_closedComplemented_of_finiteDimensional_range
  have hzero : ∀ᶠ y in 𝓝 φ.pt, φ.leftFun y = φ.leftFun φ.pt → q y = 0 := by
    apply Filter.Eventually.of_forall
    intro y hy
    apply hz y
    change r y = r x at hy
    exact hy.trans hrx
  simpa only [φ, HasStrictFDerivAt.implicitFunctionDataOfComplemented, hrx, sub_zero]
    using implicit_zero_local_bound φ (hq.hasStrictFDerivAt (by norm_num)) hzero

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Away from the zero set a continuous quotient is locally bounded. -/
theorem nonzero_local_bound {r q : E → ℝ} {x : E}
    (hr : Continuous r) (hq : Continuous q) (hrx : r x ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, ‖q y‖ ≤ C * ‖r y‖ := by
  let C := ‖q x / r x‖ + 1
  have hc : ContinuousAt (fun y => ‖q y / r y‖) x :=
    ((hq.continuousAt).div hr.continuousAt hrx).norm
  have he : ∀ᶠ y in 𝓝 x, ‖q y / r y‖ < C :=
    hc.eventually (gt_mem_nhds (by dsimp [C]; linarith))
  have hn : ∀ᶠ y in 𝓝 x, r y ≠ 0 := hr.continuousAt.eventually_ne hrx
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [he, hn] with y hy hyn
  rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr hyn)] at hy
  exact hy.le

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Compactness upgrades pointwise local domination to a uniform estimate. -/
theorem compact_local_bound {K : Set E} (hK : IsCompact K) {q r : E → ℝ}
    (hlocal : ∀ x ∈ K, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ y in 𝓝 x, ‖q y‖ ≤ C * ‖r y‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖q y‖ ≤ C * ‖r y‖ := by
  classical
  choose C hC hloc using hlocal
  let U (x : E) (hx : x ∈ K) : Set E := {y | ‖q y‖ ≤ C x hx * ‖r y‖}
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U hloc
  refine ⟨∑ x ∈ t, C x x.property, Finset.sum_nonneg (fun x _ => hC x x.property), ?_⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (ht hy)
  have hle : C x x.property ≤ ∑ z ∈ t, C z z.property :=
    Finset.single_le_sum (f := fun z : K => C z z.property)
      (fun z _ => hC z z.property) hx
  exact hxy.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))

/-- Uniform normal quotient bound on a compact set from actual regularity. -/
theorem regular_zero_compact_bound {K : Set E} (hK : IsCompact K) {r q : E → ℝ}
    (hr : ContDiff ℝ 1 r) (hq : ContDiff ℝ 1 q)
    (hrne : ∀ x ∈ K, r x = 0 → fderiv ℝ r x ≠ 0)
    (hz : ∀ y, r y = 0 → q y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖q y‖ ≤ C * ‖r y‖ := by
  apply compact_local_bound hK
  intro x hx
  by_cases hrx : r x = 0
  · exact regular_zero_local_bound hr hq (hrne x hx hrx) hrx hz
  · exact nonzero_local_bound hr.continuous hq.continuous hrx

/-- Zero-flux divergence theorem on a bounded regular sublevel set. The boundary
condition is just geometric tangency; no surface-integral theorem, quotient,
null-boundary hypothesis, or integration-by-parts premise is assumed. -/
theorem integral_divergence_zero_of_tangent [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    {I : Type*} [Fintype I] (d : I → E) (F : I → E → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) {r : E → ℝ} (hr : ContDiff ℝ 2 r)
    (hb : Bornology.IsBounded {x | r x < 0})
    (hrne : ∀ x ∈ closure {x | r x < 0}, r x = 0 → fderiv ℝ r x ≠ 0)
    (hzero : ∀ x, r x = 0 → (∑ i, fderiv ℝ r x (d i) * F i x) = 0) :
    (∫ x in {x | r x < 0}, ∑ i, fderiv ℝ (F i) x (d i)) = 0 := by
  let q := fun x => ∑ i, fderiv ℝ r x (d i) * F i x
  have hq : ContDiff ℝ 1 q := ContDiff.sum (fun i _ =>
    ((hr.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).mul (hF i))
  have hc : IsCompact (closure {x | r x < 0}) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  obtain ⟨C, _, hC⟩ := regular_zero_compact_bound hc (hr.of_le (by norm_num)) hq hrne hzero
  exact integral_divergence_zero_of_normal_bound d F hF (hr.of_le (by norm_num)) hb C
    hzero (fun x hx => hC x (subset_closure hx))

end OAI.Analysis.PDE.Green
