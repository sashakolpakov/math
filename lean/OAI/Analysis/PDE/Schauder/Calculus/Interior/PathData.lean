import OAI.Analysis.PDE.Schauder.Calculus.DensityGradientHolder
import OAI.Analysis.PDE.Dirichlet.Path.BanachBound
import OAI.Analysis.PDE.Dirichlet.Moore.RealOperator

noncomputable section
open Set Module
open scoped Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4

local instance pathDataFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance pathDataFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance pathDataSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathDataSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Uniform lower-order data already proved for the actual nonlinear path.
The constructor theorem below derives this record from the manuscript's
geometric and fixed-density assumptions. -/
structure InteriorThirdPathData (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (r B₀ F₀ F₁ : E → ℝ) (hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}) where
  exponent : ℝ
  exponent_pos : 0 < exponent
  exponent_lt_one : exponent < 1
  normBound : ℝ
  normBound_pos : 0 < normBound
  lower : ℝ
  lower_pos : 0 < lower
  upper : ℝ
  upper_nonneg : 0 ≤ upper
  densityBound : ℝ
  densityBound_nonneg : 0 ≤ densityBound
  jets : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK exponent
  jet_norm : ∀ s, ‖jets s‖ ≤ normBound
  jet_value : ∀ s (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.C2Holder.value (jets s) x = B₀ x+s.u x
  jet_first : ∀ s (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (jets s) x =
    fderiv ℝ (fun y => B₀ y+s.u y) x
  jet_second : ∀ s (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (jets s) x =
    fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y)) x
  coefficient_bounds : ∀ (s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁) (x : E), r x < 0 → ∀ v : E,
    lower*‖v‖^2 ≤ inner ℝ v
      (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x) v) ∧
    inner ℝ v (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x) v) ≤ upper*‖v‖^2
  density_norm : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, r x ≤ 0 →
    ‖fderiv ℝ (OAI.Analysis.PDE.Dirichlet.densityPath F₀ F₁ t) x‖ ≤ densityBound
  density_holder : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 →
    ‖fderiv ℝ (OAI.Analysis.PDE.Dirichlet.densityPath F₀ F₁ t) x-fderiv ℝ (OAI.Analysis.PDE.Dirichlet.densityPath F₀ F₁ t) y‖ ≤
      densityBound*dist x y^exponent

theorem nonempty_interiorThirdPathData
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+1) 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) (hBper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat B₀)
    (hp₀ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₀) (hp₁ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n+1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x-r₀ •
        (1 : Matrix (Fin (n+1)) (Fin (n+1)) (Quaternion ℝ)))).PosSemidef)
    {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} :
    Nonempty (InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) := by
  obtain ⟨α,R,hα,hα1,hR,Φ,hΦ⟩ := OAI.Analysis.PDE.Dirichlet.uniform_banach_bound_densityPath_lattice (hΩK := hΩK)
    e lat hK hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨c,C,hc,hC,hlog⟩ := OAI.Analysis.PDE.Dirichlet.uniform_ellipticity_densityPath_lattice e lat hK
    hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨a,A,L,ha,hA,hL,hden⟩ := OAI.Analysis.PDE.Dirichlet.densityPath_uniform_bounds_lattice e lat hK
    hr.continuous hrper hbounded hne hF₀ hF₁ hp₀ hp₁ hpos₀ hpos₁
  obtain ⟨B,hB,hgrad⟩ := densityPath_uniform_gradient_holder_lattice e lat hK
    hr.continuous hrper hbounded F₀ F₁ hF₀ hF₁ hp₀ hp₁ hα.le hα1.le
  refine ⟨{
    exponent := α, exponent_pos := hα, exponent_lt_one := hα1
    normBound := R, normBound_pos := hR
    lower := a*c, lower_pos := mul_pos ha hc
    upper := A*C, upper_nonneg := (mul_pos hA hC).le
    densityBound := B, densityBound_nonneg := hB.le
    jets := Φ
    jet_norm := fun s => (hΦ s).1
    jet_value := fun s => (hΦ s).2.1
    jet_first := fun s => (hΦ s).2.2.1
    jet_second := fun s => (hΦ s).2.2.2.1
    coefficient_bounds := ?_
    density_norm := fun t ht => (hgrad t ht).1
    density_holder := fun t ht => (hgrad t ht).2 }⟩
  intro s x hx v
  apply OAI.Analysis.PDE.Dirichlet.detRealOperator_elliptic_bounds _ (s.positive x hx) ha.le hc.le hC.le
  · rw [s.equation x hx]
    exact ⟨(hden s.t s.parameter x hx.le).1,(hden s.t s.parameter x hx.le).2.1⟩
  · exact hlog s.t s.parameter s.u s.smooth s.periodic s.zero s.positive s.equation x hx.le

end OAI.Analysis.PDE.Schauder
