import OAI.Analysis.PDE.Elliptic.Boundary.FlatJet
import OAI.Analysis.PDE.Elliptic.Boundary.GradientRestricted

/-! The boundary slope is the actual full differential of a function with
zero trace. Thus the interpolation estimate controls the difference of
actual differentials, not merely an independently supplied normal slope. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem flat_boundary_fderiv_eq_normal {u : E → ℝ} {z v : E}
    (hu : DifferentiableAt ℝ u z) (hv : ‖v‖ = 1) (hz : inner ℝ v z = 0)
    (hzero : ∀ᶠ y in 𝓝 z, inner ℝ v y = 0 → u y = 0) :
    fderiv ℝ u z = (fderiv ℝ u z v) • innerSL ℝ v := by
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  ext w
  let e := w - (inner ℝ v w) • v
  have he : inner ℝ v e = 0 := by
    simp only [e, inner_sub_right, real_inner_smul_right, hvv, mul_one, sub_self]
  have hde := flat_boundary_first_jet_of_local_zero hu hv hz he hzero
  change fderiv ℝ u z (w - (inner ℝ v w) • v) = 0 at hde
  rw [map_sub, map_smul] at hde
  change fderiv ℝ u z w = fderiv ℝ u z v * inner ℝ v w
  change fderiv ℝ u z w - inner ℝ v w * fderiv ℝ u z v = 0 at hde
  nlinarith

theorem fderiv_approaches_zero_trace
    {u : E → ℝ} {v z : E} {h κ A B a b : ℝ}
    (hv : ‖v‖ = 1) (hz : inner ℝ v z = 0)
    (hh : 0 < h) (hh1 : h ≤ 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b)
    (huz : DifferentiableAt ℝ u z)
    (hzero : ∀ᶠ y in 𝓝 z, inner ℝ v y = 0 → u y = 0)
    (hu : ∀ y ∈ Metric.closedBall (z + h • v) (κ * h / 2), DifferentiableAt ℝ u y)
    (hexp : ∀ y, ‖y - z‖ ≤ 2 * h → 0 ≤ inner ℝ v y →
      |u y - (fderiv ℝ u z v) * inner ℝ v y| ≤ A * h ^ a * inner ℝ v y)
    (hder : ∀ y ∈ Metric.closedBall (z + h • v) (κ * h / 2),
      ‖fderiv ℝ u y - fderiv ℝ u (z + h • v)‖ ≤ B * (‖y - (z + h • v)‖ / h) ^ b) :
    ‖fderiv ℝ u (z + h • v) - fderiv ℝ u z‖ ≤
      (8 * A / κ ^ (1 + a) + B) * h ^ (a * b / (1 + b)) := by
  rw [flat_boundary_fderiv_eq_normal huz hv hz hzero]
  exact fderiv_approaches_boundary_slope_on_smaller_ball hv hz hh hh1 hκ hκ1
    hA hB ha hb hu hexp hder

end OAI.Analysis.PDE.Elliptic
