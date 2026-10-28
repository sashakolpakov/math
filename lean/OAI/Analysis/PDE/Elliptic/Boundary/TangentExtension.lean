import OAI.Analysis.PDE.Elliptic.Boundary.TangentField
import OAI.Analysis.PDE.Elliptic.Boundary.LocalExtension

/-! Genuine globally C² test fields agreeing with the level-set tangent
fields on a neighborhood; their bounds depend only on the defining data. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem eventually_C2_norm_bounds {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x,
      ‖f y‖ ≤ C ∧ ‖fderiv ℝ f y‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 f y‖ ≤ C := by
  let C := ‖f x‖ + ‖fderiv ℝ f x‖ + ‖iteratedFDeriv ℝ 2 f x‖ + 1
  have h0 : ‖f x‖ < C := by dsimp [C]; linarith [norm_nonneg (fderiv ℝ f x), norm_nonneg (iteratedFDeriv ℝ 2 f x)]
  have h1 : ‖fderiv ℝ f x‖ < C := by dsimp [C]; linarith [norm_nonneg (f x), norm_nonneg (iteratedFDeriv ℝ 2 f x)]
  have h2 : ‖iteratedFDeriv ℝ 2 f x‖ < C := by dsimp [C]; linarith [norm_nonneg (f x), norm_nonneg (fderiv ℝ f x)]
  have hc2 : ContinuousAt (iteratedFDeriv ℝ 2 f) x := hf.continuousAt_iteratedFDeriv (by norm_num)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hf.continuousAt.norm.tendsto.eventually (eventually_lt_nhds h0),
    (hf.fderiv_right (m := 1) (by norm_num)).continuousAt.norm.tendsto.eventually (eventually_lt_nhds h1),
    hc2.norm.tendsto.eventually (eventually_lt_nhds h2)]
      with y hy0 hy1 hy2
  exact ⟨hy0.le, hy1.le, hy2.le⟩

theorem exists_bounded_level_tangent_field [FiniteDimensional ℝ E]
    {r : E → ℝ} (hr : ContDiff ℝ 3 r) (x w e : E) (hw : fderiv ℝ r x w ≠ 0) :
    ∃ (T : E → E) (R C : ℝ), 0 < R ∧ 0 < C ∧ ContDiff ℝ 2 T ∧
      ∀ y ∈ Metric.closedBall x R,
        T =ᶠ[𝓝 y] levelTangentField r w e ∧ fderiv ℝ r y w ≠ 0 ∧
        ‖T y‖ ≤ C ∧ ‖fderiv ℝ T y‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 T y‖ ≤ C := by
  have hlocal := contDiffAt_levelTangentField hr.contDiffAt w e hw
  obtain ⟨T, hT, hTeq⟩ := exists_contDiff_extension_near_compact (k := 2) (isCompact_singleton : IsCompact {x})
    (fun y hy => by simpa [Set.mem_singleton_iff.mp hy] using hlocal)
  have heq := hTeq x (mem_singleton x)
  obtain ⟨C, hC, hbound⟩ := eventually_C2_norm_bounds (hT.contDiffAt (x := x))
  have hn : ∀ᶠ y in 𝓝 x, fderiv ℝ r y w ≠ 0 :=
    (((hr.fderiv_right (m := 2) (by norm_num)).continuous.clm_apply continuous_const).tendsto x).eventually
      (eventually_ne_nhds hw)
  have hgood := (heq.eventuallyEq_nhds.and hn).and hbound
  obtain ⟨ε, hε, heps⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨T, ε / 2, C, by positivity, hC, hT, ?_⟩
  intro y hy
  have hy' := heps (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε) hy)
  exact ⟨hy'.1.1, hy'.1.2, hy'.2⟩

end OAI.Analysis.PDE.Elliptic
