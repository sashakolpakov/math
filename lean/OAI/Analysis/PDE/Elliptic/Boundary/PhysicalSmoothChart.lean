import OAI.Analysis.PDE.Elliptic.Calculus.SmoothCoordinateChart

/-! Smooth normalized boundary charts in the original coordinate space,
with a separately chosen Euclidean indexing isometry. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Elliptic

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "X" => EuclideanSpace ℝ (Fin m)

theorem exists_physical_smooth_coordinate_chart (e : X ≃ₗᵢ[ℝ] E) (k : Fin m)
    {r : E → ℝ} (hr : ContDiff ℝ ∞ r) (a : E) (hg : fderiv ℝ r a ≠ 0) :
    ∃ (c : ℝ) (G P : E → E), 0 < c ∧ ContDiff ℝ ∞ G ∧ ContDiff ℝ ∞ P ∧
      G 0 = a ∧ ∀ z ∈ closedBall 0 2,
        (fun y => P (G y)) =ᶠ[𝓝 z] id ∧ r (G z)-r a = -c*(e.symm z) k := by
  have hd : fderiv ℝ (r ∘ e) (e.symm a) =
      (fderiv ℝ r a).comp e.toContinuousLinearEquiv.toContinuousLinearMap := by
    have h := ((hr.differentiable (by simp) (e (e.symm a))).hasFDerivAt.comp
      (e.symm a) e.toContinuousLinearEquiv.hasFDerivAt).fderiv
    simpa only [e.apply_symm_apply] using h
  have hne : fderiv ℝ (r ∘ e) (e.symm a) ≠ 0 := by
    intro hz
    apply hg
    ext v
    have heq := congrArg (fun L : X →L[ℝ] ℝ => L (e.symm v)) hz
    rw [hd] at heq
    change (fderiv ℝ r a) (e (e.symm v)) = 0 at heq
    change (fderiv ℝ r a) v = 0
    simpa only [e.apply_symm_apply] using heq
  obtain ⟨c, _, G₀, P₀, hc, _, hG₀, hP₀, hGzero, hchart⟩ :=
    exists_smooth_bounded_coordinate_chart k (hr.comp e.contDiff) (e.symm a) hne
      isOpen_univ (mem_univ _)
  let G : E → E := fun z => e (G₀ (e.symm z))
  let P : E → E := fun z => e (P₀ (e.symm z))
  refine ⟨c, G, P, hc, e.contDiff.comp (hG₀.comp e.symm.contDiff),
    e.contDiff.comp (hP₀.comp e.symm.contDiff), ?_, ?_⟩
  · simp only [G, map_zero, hGzero, e.apply_symm_apply]
  · intro z hz
    have hb : e.symm z ∈ closedBall 0 2 := by
      simpa only [mem_closedBall, dist_zero_right, e.symm.norm_map] using hz
    have hch := hchart (e.symm z) hb
    constructor
    · have h := hch.2.1.comp_tendsto (e.symm.continuous.tendsto z)
      filter_upwards [h] with y hy
      change e (P₀ (e.symm (e (G₀ (e.symm y))))) = y
      change P₀ (G₀ (e.symm y)) = e.symm y at hy
      rw [e.symm_apply_apply, hy, e.apply_symm_apply]
    · simpa only [G, Function.comp_apply, e.apply_symm_apply] using hch.2.2.1

end OAI.Analysis.PDE.Elliptic
