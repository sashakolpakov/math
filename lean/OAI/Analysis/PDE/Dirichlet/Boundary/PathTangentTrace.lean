import OAI.Analysis.PDE.Elliptic.Boundary.ContinuousJet
import OAI.Analysis.PDE.Dirichlet.Path.LimitData

/-! Tangential boundary data for the actual compactness limit. -/

noncomputable section
open Set Filter Module
open scoped Topology
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
  {r B₀ F₀ F₁ : CoordinateSpace n 4 → ℝ}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {β t : ℝ}
  {s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁}

/-- The first jet of a Banach path limit has the prescribed tangential
boundary trace. Neither a C³ extension nor a boundary derivative is assumed. -/
theorem BanachPathLimit.chart_tangential_trace
    (L : BanachPathLimit e lat r B₀ F₀ F₁ hΩK β s t)
    {S : Set (CoordinateSpace n 4)} (hS : IsOpen S) (hconv : Convex ℝ S)
    {G : CoordinateSpace n 4 → CoordinateSpace n 4} (hG : ContDiff ℝ 1 G)
    (hGK : MapsTo G (closure S) {x | r x ≤ 0})
    (hGΩ : MapsTo G S {x | r x < 0})
    {x v : CoordinateSpace n 4} (hx : x ∈ closure S)
    (hB : DifferentiableAt ℝ B₀ (G x))
    (hline : ∀ᶠ q : ℝ in 𝓝 0, x + q • v ∈ closure S)
    (hzero : ∀ᶠ q : ℝ in 𝓝 0, r (G (x + q • v)) = 0) :
    (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative L.value ⟨G x, hGK hx⟩ - fderiv ℝ B₀ (G x))
      (fderiv ℝ G x v) = 0 := by
  have hh := L.value.chart_tangential_trace_eq hS hconv hG hGK hGΩ hx hB hline
    (show ∀ᶠ q : ℝ in 𝓝 0,
      OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value) (G (x + q • v)) = B₀ (G (x + q • v)) from by
        filter_upwards [hline, hzero] with q hq hrq
        rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ (hGK hq)]
        exact L.boundary ⟨G (x + q • v), hGK hq⟩ hrq)
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ (hGK hx)] at hh
  simpa only [sub_apply, sub_eq_zero] using hh

end OAI.Analysis.PDE.Dirichlet
