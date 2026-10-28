import OAI.AlgebraicTopology.DeRham.Comparison.RadialOne
import Mathlib.Topology.Compactness.Compact

/-! # Radial Localization -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RadialLocalization

noncomputable section

/-!
# Local dependence of the actual radial integral

The integral at a point depends only on the form along its radial segment.
Agreement near that compact segment implies agreement of the resulting
radial primitives on a neighborhood of the point.
-/

open Filter Set _root_.MeasureTheory
open scoped _root_.Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ}

/-- The radial primitive depends only on the values along the radial segment. -/
theorem radialHomotopy_congr_segment
    {form other : E → E [⋀^Fin (n + 1)]→L[ℝ] F} {x : E}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, form (t • x) = other (t • x)) :
    RadialOne.radialHomotopy form x = RadialOne.radialHomotopy other x := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  simp only [RadialOne.radialIntegrand, h t ht']

/-- Agreement of forms near a compact radial segment implies agreement of
their actual radial integrals near its endpoint. -/
theorem radialHomotopy_eventuallyEq_of_nhdsSegment
    {form other : E → E [⋀^Fin (n + 1)]→L[ℝ] F} {x : E}
    (h : form =ᶠ[𝓝ˢ (segment ℝ (0 : E) x)] other) :
    RadialOne.radialHomotopy form =ᶠ[𝓝 x] RadialOne.radialHomotopy other := by
  have hlocal : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ᶠ z : E × ℝ in 𝓝 (x, t), form (z.2 • z.1) = other (z.2 • z.1) := by
    intro t ht
    have hmem : t • x ∈ segment ℝ (0 : E) x := by
      rw [segment_eq_image]
      exact ⟨t, ht, by simp⟩
    have hpoint : form =ᶠ[𝓝 (t • x)] other := h.filter_mono (nhds_le_nhdsSet hmem)
    exact hpoint.comp_tendsto (continuous_snd.smul continuous_fst).continuousAt
  have hall : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1,
      form (t • y) = other (t • y) :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).eventually_forall_of_forall_eventually
      (x₀ := x) (P := fun y t => form (t • y) = other (t • y)) hlocal
  filter_upwards [hall] with y hy
  exact radialHomotopy_congr_segment hy

end

end OAI.AlgebraicTopology.DeRham.Comparison.RadialLocalization
