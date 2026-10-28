import OAI.Analysis.PDE.Green.LocalExtension
import OAI.Analysis.PDE.Elliptic.Boundary.NormalHolder

/-! Localization of the boundary estimate. No extension of a solution or its
equation through the artificial outer edge of a chart is assumed. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_contDiff_extension_near_compact {K : Set E} (hK : IsCompact K)
    {f : E → F} {k : ℕ} (hf : ∀ x ∈ K, ContDiffAt ℝ k f x) :
    ∃ g : E → F, ContDiff ℝ k g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  let U : Set E := {x | ContDiffAt ℝ k f x}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun x hx =>
    (show ContDiffAt ℝ k f x from hx).eventually (by simp)
  obtain ⟨χ, hχ, _, hχone, hχzero⟩ :=
    OAI.Analysis.PDE.Green.exists_smooth_cutoff_near_compact hK hU hf (k := (k : ℕ∞))
  refine ⟨fun x => χ x • f x, OAI.Analysis.PDE.Green.contDiff_cutoff_smul hU hχ hχzero
    (fun x hx => (show ContDiffAt ℝ k f x from hx).contDiffWithinAt), ?_⟩
  intro x hx
  filter_upwards [hχone x hx] with y hy
  simp only [hy, one_smul]

theorem ellipticTrace_congr_germ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E → E →L[ℝ] E) {f g : E → ℝ} {x : E}
    (hfg : f =ᶠ[𝓝 x] g) : ellipticTrace A f x = ellipticTrace A g x := by
  have hgrad : gradient f =ᶠ[𝓝 x] gradient g := by
    filter_upwards [hfg.eventuallyEq_nhds] with y hy
    exact congrArg ((toDual ℝ E).symm) (hy.fderiv_eq (𝕜 := ℝ))
  simp only [ellipticTrace, hgrad.fderiv_eq (𝕜 := ℝ)]

/-- The flat-boundary normal-derivative estimate requires smoothness only
near the closed half-ball. Its equation remains an interior assumption. -/
theorem boundary_normal_holder_local
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ m M K : ℝ, m ≤ M → 0 ≤ K →
      ∃ C : ℝ, 0 < C ∧
      ∀ (v : EuclideanSpace ℝ ι), ‖v‖ = 1 →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (u : EuclideanSpace ℝ ι → ℝ),
      (∀ x ∈ closedHalfBall v, ContDiffAt ℝ 2 u x) →
      (∀ x ∈ closedHalfBall v, m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x) →
      (∀ x ∈ closedHalfBall v, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w (A x w)) →
      (∀ x ∈ closedHalfBall v, ∀ w, inner ℝ w (A x w) ≤ L * ‖w‖ ^ 2) →
      (∀ x ∈ openHalfBall v, |ellipticTrace A u x| ≤ 2 * K * lam * Fintype.card ι) →
      ∀ z z', ‖z‖ ≤ 1 / 8 → ‖z'‖ ≤ 1 / 8 → inner ℝ v z = 0 → inner ℝ v z' = 0 →
        |fderiv ℝ u z v - fderiv ℝ u z' v| ≤ C * ‖z - z'‖ ^ α := by
  obtain ⟨α, hα, hα1, hbound⟩ := boundary_normal_holder (ι := ι) hlam hL
  refine ⟨α, hα, hα1, ?_⟩
  intro m M K hm hK
  obtain ⟨C, hC, hbound⟩ := hbound m M K hm hK
  refine ⟨C, hC, ?_⟩
  intro v hv A u hu hb hlo hhi hLu z z' hz hz' hvz hvz'
  have hc : IsCompact (closedHalfBall v) := by
    have he : closedHalfBall v = Metric.closedBall 0 1 ∩ {x | 0 ≤ inner ℝ v x} := by
      ext x
      simp [closedHalfBall, Metric.mem_closedBall, dist_zero_right]
    rw [he]
    exact (isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const (continuous_const.inner continuous_id))
  obtain ⟨g, hg, hgu⟩ := exists_contDiff_extension_near_compact hc hu
  have hzmem : z ∈ closedHalfBall v := ⟨by linarith, by simp [hvz]⟩
  have hzmem' : z' ∈ closedHalfBall v := ⟨by linarith, by simp [hvz']⟩
  rw [← (hgu z hzmem).fderiv_eq (𝕜 := ℝ), ← (hgu z' hzmem').fderiv_eq (𝕜 := ℝ)]
  apply hbound v hv A g hg _ hlo hhi _ z z' hz hz' hvz hvz'
  · intro x hx
    rw [(hgu x hx).eq_of_nhds]
    exact hb x hx
  · intro x hx
    rw [ellipticTrace_congr_germ A (hgu x ⟨hx.1.le, hx.2.le⟩)]
    exact hLu x hx

end OAI.Analysis.PDE.Elliptic
