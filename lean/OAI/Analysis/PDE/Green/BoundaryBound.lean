import OAI.Analysis.PDE.Green.RegularBoundary

/-! A small value on a regular level set extends with an error linear in the
defining function. The constants come from the actual inverse function theorem. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem implicit_boundary_local_bound
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (φ : ImplicitFunctionData ℝ E ℝ G) {q : E → ℝ} {q' : E →L[ℝ] ℝ} {B : ℝ}
    (hq : HasStrictFDerivAt q q' φ.pt)
    (hz : ∀ᶠ y in 𝓝 φ.pt, φ.leftFun y = φ.leftFun φ.pt → ‖q y‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 φ.pt,
      ‖q y‖ ≤ B + C * ‖φ.leftFun y - φ.leftFun φ.pt‖ := by
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
    simpa only [R, Function.comp_def, Function.uncurry_apply_pair,
      ImplicitFunctionData.prodFun_apply, hbase] using hG.continuousAt.tendsto.comp hfix
  refine ⟨(L : ℝ) * K, by positivity, ?_⟩
  filter_upwards [hV, hR hV, φ.hasStrictFDerivAt.continuousAt.tendsto hU,
    hfix hU, φ.implicitFunction_apply_image,
    φ.leftFun_implicitFunction_eq_leftFun, hR hz] with y hy hRy hUy hUfy hIy hrY hzY
  have hqR : ‖q (R y)‖ ≤ B := hzY hrY
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
  have hqdiff : dist (q y) (q (R y)) ≤
      (L : ℝ) * ((K : ℝ) * ‖φ.leftFun y - φ.leftFun φ.pt‖) :=
    (hLV.dist_le_mul _ hy _ hRy).trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)
  have htri : ‖q y‖ ≤ dist (q y) (q (R y)) + ‖q (R y)‖ := by
    simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (q y - q (R y)) (q (R y))
  nlinarith

theorem regular_boundary_local_bound {r q : E → ℝ} {x : E} {B : ℝ}
    (hr : ContDiff ℝ 1 r) (hq : ContDiff ℝ 1 q)
    (hrne : fderiv ℝ r x ≠ 0) (hrx : r x = 0)
    (hz : ∀ y, r y = 0 → ‖q y‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, ‖q y‖ ≤ B + C * ‖r y‖ := by
  let r' := fderiv ℝ r x
  let hsurj := OAI.Analysis.PDE.Dirichlet.real_linear_form_range_top r' hrne
  let φ := (hr.hasStrictFDerivAt (by norm_num) (x := x)).implicitFunctionDataOfComplemented
    r r' hsurj r'.ker_closedComplemented_of_finiteDimensional_range
  have hzero : ∀ᶠ y in 𝓝 φ.pt, φ.leftFun y = φ.leftFun φ.pt → ‖q y‖ ≤ B := by
    apply Filter.Eventually.of_forall
    intro y hy
    apply hz y
    change r y = r x at hy
    exact hy.trans hrx
  simpa only [φ, HasStrictFDerivAt.implicitFunctionDataOfComplemented, hrx, sub_zero]
    using implicit_boundary_local_bound φ (hq.hasStrictFDerivAt (by norm_num)) hzero

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem compact_boundary_local_bound {K : Set E} (hK : IsCompact K) {q r : E → ℝ} {B : ℝ}
    (hlocal : ∀ x ∈ K, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ y in 𝓝 x, ‖q y‖ ≤ B + C * ‖r y‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖q y‖ ≤ B + C * ‖r y‖ := by
  classical
  choose C hC hloc using hlocal
  let U (x : E) (hx : x ∈ K) : Set E := {y | ‖q y‖ ≤ B + C x hx * ‖r y‖}
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U hloc
  refine ⟨∑ x ∈ t, C x x.property, Finset.sum_nonneg (fun x _ => hC x x.property), ?_⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (ht hy)
  have hle : C x x.property ≤ ∑ z ∈ t, C z z.property :=
    Finset.single_le_sum (f := fun z : K => C z z.property)
      (fun z _ => hC z z.property) hx
  exact hxy.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hle (norm_nonneg _)))

theorem regular_boundary_compact_bound {K : Set E} (hK : IsCompact K) {r q : E → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hr : ContDiff ℝ 1 r) (hq : ContDiff ℝ 1 q)
    (hrne : ∀ x ∈ K, r x = 0 → fderiv ℝ r x ≠ 0)
    (hz : ∀ y, r y = 0 → ‖q y‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖q y‖ ≤ B + C * ‖r y‖ := by
  apply compact_boundary_local_bound hK
  intro x hx
  by_cases hrx : r x = 0
  · exact regular_boundary_local_bound hr hq (hrne x hx hrx) hrx hz
  · obtain ⟨C, hC, hc⟩ := nonzero_local_bound hr.continuous hq.continuous hrx
    refine ⟨C, hC, hc.mono (fun y hy => ?_)⟩
    linarith

end OAI.Analysis.PDE.Green
