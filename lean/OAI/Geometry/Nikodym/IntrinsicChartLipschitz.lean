import OAI.Geometry.Nikodym.IntrinsicChartMaps

noncomputable section
namespace OAI.Geometry.Nikodym.LocalBeltramiChart

open Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {g : SmoothCoordinateMetric E} {κ : ℝ} {x₀ : E}
variable (C : LocalBeltramiChart g κ x₀)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Local chart distortion combines with the actual intrinsic lower
metric estimate. -/
theorem intrinsicForward_lipschitz {A K : NNReal}
    (ha : LipschitzWith A (OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g))
    {P : Set E} (hP : P ⊆ C.chart.source) (hk : LipschitzOnWith K (C.chart : E → E) P) :
    LipschitzOnWith (K*A) C.intrinsicForward (OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g ⁻¹' P) := by
  intro x hx y hy
  rw [C.intrinsicForward_eq (hP hx),C.intrinsicForward_eq (hP hy)]
  calc
    _ ≤ (K : ℝ≥0∞) * edist (OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g x) (OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g y) := hk hx hy
    _ ≤ (K : ℝ≥0∞) * ((A : ℝ≥0∞) * edist x y) := mul_le_mul' le_rfl (ha x y)
    _ = ((K*A : NNReal) : ℝ≥0∞) * edist x y := by simp [mul_assoc]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The inverse chart is Lipschitz for the genuine intrinsic metric,
using the proved convex-domain upper metric estimate. -/
theorem intrinsicInverse_lipschitz {B L : NNReal}
    (hb : LipschitzWith B (OAI.Geometry.Nikodym.IntrinsicDomain.ofCoordinate g))
    {V : Set E} (hV : V ⊆ C.chart.target) (hl : LipschitzOnWith L (C.chart.symm : E → E) V) :
    LipschitzOnWith (B*L) C.intrinsicInverse V := by
  intro x hx y hy
  have h := hb (show g.openDomain from C.intrinsicInverse x)
    (show g.openDomain from C.intrinsicInverse y)
  change edist (C.intrinsicInverse x) (C.intrinsicInverse y) ≤
    (B : ℝ≥0∞) * edist (OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g (C.intrinsicInverse x))
      (OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g (C.intrinsicInverse y)) at h
  rw [C.coordinate_intrinsicInverse (hV hx),C.coordinate_intrinsicInverse (hV hy)] at h
  calc
    _ ≤ (B : ℝ≥0∞) * edist (C.chart.symm x) (C.chart.symm y) := h
    _ ≤ (B : ℝ≥0∞) * ((L : ℝ≥0∞) * edist x y) := mul_le_mul' le_rfl (hl hx hy)
    _ = ((B*L : NNReal) : ℝ≥0∞) * edist x y := by simp [mul_assoc]

end OAI.Geometry.Nikodym.LocalBeltramiChart
