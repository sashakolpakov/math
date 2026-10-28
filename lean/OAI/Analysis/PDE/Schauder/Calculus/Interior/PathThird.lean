import OAI.Analysis.PDE.Schauder.Calculus.Interior.PathData
import OAI.Analysis.PDE.Schauder.Calculus.Interior.MooreGlobalJet

noncomputable section
open Set Metric Module
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance pathThirdFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance pathThirdFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance pathThirdSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathThirdSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathThirdThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathThirdThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- A single local radius and constants work for every actual smooth
solution along the fixed nonlinear density path. The data record is
constructed unconditionally by `nonempty_interiorThirdPathData`. -/
theorem InteriorThirdPathData.local_third_estimate
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) (hn : 3 ≤ n*4)
    (hr : Continuous r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (x₀ : E) (hx₀ : r x₀ < 0) :
    ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁,
      ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) d.exponent,
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x =
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y))) x) →
      (∀ x ∈ closedBall x₀ δ,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y))) x‖ ≤ ε*‖T‖+D) ∧
      (∀ x ∈ closedBall x₀ δ, ∀ y ∈ closedBall x₀ δ,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+s.u z))) x-
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+s.u z))) y‖ ≤ (ε*‖T‖+D)*‖x-y‖^d.exponent) := by
  have hO : IsOpen {x | r x < 0} := isOpen_lt hr continuous_const
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hO x₀ hx₀
  have hcball : closedBall x₀ (ρ/2) ⊆ {x | r x < 0} :=
    (closedBall_subset_ball (half_lt_self hρ)).trans hball
  obtain ⟨δ,hδ,hlocal⟩ := moore_interior_third_global_jet_schauder (hΓK := hΩK)
    hn (OAI.Analysis.PDE.Dirichlet.flattenFourSlots n).symm hO hΩK d.exponent_pos d.exponent_lt_one d.lower_pos
    d.upper_nonneg d.normBound_pos.le (half_pos hρ) x₀ hcball
  refine ⟨δ,hδ,?_⟩
  intro ε hε
  obtain ⟨D₀,hD₀,hestimate⟩ := hlocal ε hε
  let D := D₀*(d.densityBound+d.normBound)+1
  have hD : 0 < D := by
    dsimp only [D]
    have hb := d.densityBound_nonneg
    have hR := d.normBound_pos
    positivity
  refine ⟨D,hD,?_⟩
  intro s T hT
  have hh := hestimate (fun y => B₀ y+s.u y) (OAI.Analysis.PDE.Dirichlet.densityPath F₀ F₁ s.t)
    (hB₀.add s.smooth) ((OAI.Analysis.PDE.Dirichlet.contDiff_densityPath hF₀ hF₁ s.t).differentiable (by norm_num)).differentiableOn
    s.equation (d.jets s) (d.jet_norm s) (d.jet_value s) (d.jet_first s) (d.jet_second s)
    (fun v => (d.coefficient_bounds s x₀ hx₀ v).1)
    (fun v => (d.coefficient_bounds s x₀ hx₀ v).2) T hT d.densityBound d.densityBound_nonneg
    (fun x hx => d.density_norm s.t s.parameter x hx.le)
    (fun x hx y hy => d.density_holder s.t s.parameter x hx.le y hy.le)
  have hbudget : ε*‖T‖+D₀*(d.densityBound+d.normBound) ≤ ε*‖T‖+D := by
    dsimp only [D]
    linarith
  constructor
  · intro x hx
    exact (hh.1 x hx).trans hbudget
  · intro x hx y hy
    exact (hh.2 x hx y hy).trans
      (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
