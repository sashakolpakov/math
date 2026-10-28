import OAI.Analysis.PDE.Elliptic.Calculus.SmoothNormalizedChart
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Constants
import OAI.Analysis.PDE.Schauder.Boundary.SchauderNormalization

noncomputable section
open Set Filter Metric InnerProductSpace
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Elliptic

theorem compact_C4_derivative_bounds {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ 4 f) {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K,
      ‖fderiv ℝ f x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 f x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ 3 f x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 4 f x‖ ≤ C := by
  obtain ⟨A,hA,hAjet⟩ := compact_C3_derivative_bounds (hf.of_le (by norm_num)) hK
  have hc : Continuous (iteratedFDeriv ℝ 4 f) := continuous_iff_continuousAt.mpr
    (fun x => hf.contDiffAt.continuousAt_iteratedFDeriv (by norm_num))
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max A B,hA.trans (le_max_left _ _),?_⟩
  intro x hx
  obtain ⟨h₁,h₂,h₃⟩ := hAjet x hx
  exact ⟨h₁.trans (le_max_left _ _),h₂.trans (le_max_left _ _),h₃.trans (le_max_left _ _),
    (hB x hx).trans (le_max_right _ _)⟩

/-- C∞ version of the bounded normalized coordinate chart. Its first
eight conclusions match the C³ chart; fixed fourth-derivative control
is added for both the chart and its inverse. -/
theorem exists_smooth_bounded_coordinate_chart {m : ℕ} (k : Fin m)
    {r : EuclideanSpace ℝ (Fin m) → ℝ} (hr : ContDiff ℝ ∞ r)
    (x : EuclideanSpace ℝ (Fin m)) (hg : fderiv ℝ r x ≠ 0)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (c C : ℝ) (G P : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)),
      0 < c ∧ 1 ≤ C ∧ ContDiff ℝ ∞ G ∧ ContDiff ℝ ∞ P ∧ G 0 = x ∧
      ∀ z ∈ closedBall 0 2,
        G z ∈ U ∧ (fun y => P (G y)) =ᶠ[𝓝 z] id ∧
        r (G z)-r x = -c*z k ∧
        ‖fderiv ℝ G z‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 G z‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 3 G z‖ ≤ C ∧ ‖fderiv ℝ P (G z)‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 4 G z‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 P (G z)‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 3 P (G z)‖ ≤ C ∧ ‖iteratedFDeriv ℝ 4 P (G z)‖ ≤ C := by
  let E := EuclideanSpace ℝ (Fin m)
  obtain ⟨v,c,G₀,P₀,hv,hc,hG₀,hP₀,hGzero,hchart⟩ :=
    exists_smooth_doubled_boundary_chart hr x hg hU hxU
  let e : E := EuclideanSpace.single k 1
  have he : ‖e‖ = 1 := by
    change ‖(EuclideanSpace.single k (1:ℝ) : EuclideanSpace ℝ (Fin m))‖ = 1
    simp
  let Q := Submodule.reflection (ℝ ∙ (e-v))ᗮ
  have hQ : Q e = v := Submodule.reflection_sub (he.trans hv.symm)
  let G := fun y : E => G₀ (Q y)
  let P := fun y : E => Q.symm (P₀ y)
  have hG : ContDiff ℝ ∞ G := hG₀.comp Q.contDiff
  have hP : ContDiff ℝ ∞ P := Q.symm.contDiff.comp hP₀
  obtain ⟨C₁,hC₁,hB₁⟩ := compact_C4_derivative_bounds (hG.of_le (by simp))
    (isCompact_closedBall (0:E) 2)
  obtain ⟨C₂,hC₂,hB₂⟩ := compact_C4_derivative_bounds (hP.of_le (by simp))
    ((isCompact_closedBall (0:E) 2).image hG.continuous)
  refine ⟨c,max C₁ C₂,G,P,hc,hC₁.trans (le_max_left _ _),hG,hP,?_,?_⟩
  · simpa only [G,map_zero] using hGzero
  · intro z hz
    have hzQ : Q z ∈ closedBall 0 2 := by
      simpa only [mem_closedBall,dist_zero_right,Q.norm_map] using hz
    have hch := hchart (Q z) hzQ
    have hinv : (fun y => P (G y)) =ᶠ[𝓝 z] id := by
      have hh := hch.2.1.comp_tendsto (Q.continuous.tendsto z)
      filter_upwards [hh] with y hy
      change Q.symm (P₀ (G₀ (Q y))) = y
      change P₀ (G₀ (Q y)) = Q y at hy
      rw [hy,Q.symm_apply_apply]
    have hnormal : inner ℝ v (Q z) = z k := by
      rw [← hQ,Q.inner_map_map]
      change inner ℝ (EuclideanSpace.single k (1:ℝ)) z = z k
      simp only [EuclideanSpace.inner_single_left,map_one,one_mul]
    obtain ⟨h₁,h₂,h₃,h₄⟩ := hB₁ z hz
    obtain ⟨hP₁,hP₂,hP₃,hP₄⟩ := hB₂ (G z) ⟨z,hz,rfl⟩
    exact ⟨hch.1,hinv,hch.2.2.trans (congrArg (fun t : ℝ => -c*t) hnormal),
      h₁.trans (le_max_left _ _),h₂.trans (le_max_left _ _),h₃.trans (le_max_left _ _),
      hP₁.trans (le_max_right _ _),h₄.trans (le_max_left _ _),hP₂.trans (le_max_right _ _),
      hP₃.trans (le_max_right _ _),hP₄.trans (le_max_right _ _)⟩

end OAI.Analysis.PDE.Elliptic
