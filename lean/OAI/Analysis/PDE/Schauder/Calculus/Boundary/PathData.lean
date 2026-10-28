import OAI.Analysis.PDE.Schauder.Calculus.Boundary.PathBounds
import OAI.Analysis.PDE.Schauder.Calculus.DensityLogGradient
import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.Solution

noncomputable section
open Set Module InnerProductSpace
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance boundaryPathFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance boundaryPathFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance boundaryPathSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance boundaryPathSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance boundaryPathEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance boundaryPathEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance

/-- Actual bounded log-coefficient and log-density-gradient fields for
the original path, retaining its already chosen Hölder exponent. -/
structure BoundaryThirdPathData
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) where
  coefficientBound : ℝ
  coefficientBound_nonneg : 0 ≤ coefficientBound
  gradientBound : ℝ
  gradientBound_pos : 0 < gradientBound
  lower : ℝ
  lower_pos : 0 < lower
  upper : ℝ
  upper_nonneg : 0 ≤ upper
  coefficients : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁ →
    OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E) d.exponent
  gradients : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁ →
    OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) d.exponent
  coefficient_norm : ∀ s, ‖coefficients s‖ ≤ coefficientBound
  gradient_norm : ∀ s, ‖gradients s‖ ≤ gradientBound
  coefficient_value : ∀ s (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.HolderMap.value (coefficients s) x =
    OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x)
  gradient_value : ∀ s (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.HolderMap.value (gradients s) x =
    (OAI.Analysis.PDE.Dirichlet.densityPath F₀ F₁ s.t x)⁻¹ • fderiv ℝ (OAI.Analysis.PDE.Dirichlet.densityPath F₀ F₁ s.t) x
  ellipticity : ∀ (s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁) (x : E), r x ≤ 0 → ∀ v : E,
    lower*‖v‖^2 ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x) v) ∧
    inner ℝ v (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x) v) ≤ upper*‖v‖^2

theorem nonempty_boundaryThirdPathData
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ 1 r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) (hp₀ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₀) (hp₁ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    Nonempty (BoundaryThirdPathData d) := by
  obtain ⟨a,b,_,ha,hb,_,hden⟩ := OAI.Analysis.PDE.Dirichlet.densityPath_uniform_bounds_lattice e lat hK hr.continuous
    hrper hbounded hne hF₀ hF₁ hp₀ hp₁ hpos₀ hpos₁
  obtain ⟨N,hN,hcoefficient⟩ := OAI.Analysis.PDE.Elliptic.exists_actual_log_coefficient_bound (hΩK := hΩK)
    d.exponent_pos.le d.normBound_pos.le ha
  have hd (s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁) (x : E) (hx : r x ≤ 0) :
      a ≤ OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x) ∧
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x) ≤ b := by
    rw [path_equation_on_closed_sublevel hr hreg hB₀ hF₀ hF₁ s x hx]
    exact ⟨(hden s.t s.parameter x hx).1,(hden s.t s.parameter x hx).2.1⟩
  have haField (s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁) :=
    hcoefficient (fun y => B₀ y+s.u y) (d.jets s) (d.jet_norm s) (d.jet_second s)
      (fun x hx => (hd s x hx).1)
  choose A hAn hA using haField
  obtain ⟨Z,hZ,hgradient⟩ := densityPath_uniform_log_gradient_holder e lat hK hr.continuous
    hrper hbounded hne F₀ F₁ hF₀ hF₁ hp₀ hp₁ hpos₀ hpos₁ d.exponent_pos.le d.exponent_lt_one.le
  have hwField (s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁) := hgradient s.t s.parameter
  choose W hWn hW using hwField
  refine ⟨{
    coefficientBound := N
    coefficientBound_nonneg := hN
    gradientBound := Z
    gradientBound_pos := hZ
    lower := d.lower/b
    lower_pos := div_pos d.lower_pos hb
    upper := d.upper/a
    upper_nonneg := div_nonneg d.upper_nonneg ha.le
    coefficients := A
    gradients := W
    coefficient_norm := hAn
    gradient_norm := hWn
    coefficient_value := hA
    gradient_value := hW
    ellipticity := ?_ }⟩
  intro s x hx v
  exact log_bounds_of_determinant_bounds _ ha hb d.lower_pos.le d.upper_nonneg
    (hd s x hx) (d.closed_coefficient_bounds hr hreg hB₀ s x hx) v

end OAI.Analysis.PDE.Schauder
