import OAI.Analysis.PDE.Schauder.Calculus.Boundary.PathData

noncomputable section
open Set Filter Module
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Elliptic

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance pathSolutionFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance pathSolutionFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance pathSolutionSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathSolutionSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Every actual path solution supplies the nonlinear boundary-estimate
record. The differentiated equation is not a premise: only the original
Moore equation, already part of `SmoothPathSolution`, is used. -/
def BoundaryThirdPathData.toBoundaryLogSolution
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    {d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK} (b : BoundaryThirdPathData d)
    (hr : Continuous r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    {m : ℕ} (e₀ : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] E) (k : Fin m)
    (S : Set E) (G : E → E) (hGΩ : MapsTo G S {x | r x < 0})
    (hboundary : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (1/2),
      x k = 0 → r (G (e₀ x)) = 0)
    (s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁) :
    OAI.Analysis.PDE.Elliptic.BoundaryLogSolution e₀ k hΩK S G B₀ d.exponent d.normBound
      b.coefficientBound b.gradientBound b.lower b.upper where
  u := fun y => B₀ y+s.u y
  f := OAI.Analysis.PDE.Dirichlet.densityPath F₀ F₁ s.t
  U := d.jets s
  A := b.coefficients s
  W := b.gradients s
  smooth := hB₀.add s.smooth
  norm_U := d.jet_norm s
  norm_A := b.coefficient_norm s
  norm_W := b.gradient_norm s
  value_U := d.jet_value s
  first_U := d.jet_first s
  second_U := d.jet_second s
  value_A := b.coefficient_value s
  value_W := b.gradient_value s
  source_differentiable := fun x _ => (OAI.Analysis.PDE.Dirichlet.contDiff_densityPath hF₀ hF₁ s.t).differentiable (by norm_num) (G x)
  equation := by
    intro x hx
    filter_upwards [(isOpen_lt hr continuous_const).mem_nhds (hGΩ hx)] with y hy
    exact s.equation y hy
  lower := fun x hx v => (b.ellipticity s x hx v).1
  upper := fun x hx v => (b.ellipticity s x hx v).2
  trace := by
    intro x hx hxk
    rw [s.zero _ (hboundary x hx hxk),add_zero]

end OAI.Analysis.PDE.Schauder
