import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.ThirdData

/-! The local full third-order estimate at a flattened boundary for the
actual nonlinear Moore equation. All derivative equations and global
Hölder extensions are constructed in `CalculusBoundaryThirdData`. -/

noncomputable section
open Set Filter Metric InnerProductSpace
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Schauder

variable {m n : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin m)
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance thirdEstimateFirstGroup : NormedAddCommGroup (X →L[ℝ] ℝ) := inferInstance
local instance thirdEstimateFirstSpace : NormedSpace ℝ (X →L[ℝ] ℝ) := inferInstance
local instance thirdEstimateSecondGroup : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance thirdEstimateSecondSpace : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance thirdEstimateThirdGroup : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance thirdEstimateThirdSpace : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance

theorem nonlinear_boundary_third_estimate
    (hm : 3 ≤ m) (e : X ≃ₗᵢ[ℝ] E) (k : Fin m)
    {Ω K S : Set E} (hΩK : Ω ⊆ K) (hΩ : IsOpen Ω) (hS : IsOpen S)
    (hconv : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (hinclude : closedCoordinateHalfPatch k 0 (1/2) ⊆ e ⁻¹' closure S)
    (hinterior : ∀ x ∈ ball (0 : X) (1/8), 0 < x k → e x ∈ S)
    (G P : E → E) (hG : ContDiff ℝ 4 G) (hP : ContDiff ℝ 4 P)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    (hinv : ∀ x ∈ closure S, (fun z => P (G z)) =ᶠ[𝓝 x] id)
    (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 4 B₀)
    {α R N Z ell Λ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hR : 0 ≤ R) (hN : 0 ≤ N) (hZ : 0 ≤ Z) (hell : 0 < ell) (hΛ : 0 ≤ Λ) :
    ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ p : BoundaryLogSolution e k hΩK S G B₀ α R N Z ell Λ,
      ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap (e ⁻¹' closure S) (X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) α,
      (∀ x : e ⁻¹' closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x =
        fderiv ℝ (fderiv ℝ (fderiv ℝ p.flatFunction)) x) →
      (∀ x ∈ ball 0 δ, 0 ≤ x k →
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ p.flatFunction)) x‖ ≤ ε*‖T‖+D) ∧
      ∀ x ∈ ball 0 δ, 0 ≤ x k → ∀ y ∈ ball 0 δ, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ p.flatFunction)) x-
          fderiv ℝ (fderiv ℝ (fderiv ℝ p.flatFunction)) y‖ ≤
            (ε*‖T‖+D)*‖x-y‖^α := by
  obtain ⟨ell',Λ',N',B,V,hell',hΛ',hN',hB,hV,hdata⟩ :=
    exists_uniform_flat_third_equation e k hΩK hΩ hS hconv hcompact hdiam hinclude hinterior
      G P hG hP hGK hGΩ hinv B₀ hB₀ hα hα1 hR hN hZ hell hΛ
  obtain ⟨δ,hδ,hestimate⟩ := boundary_third_norm_schauder hm k
    (isOpen_empty : IsOpen (∅ : Set X)) (empty_subset (e ⁻¹' closure S)) hinclude
    hα hα1 hell' hΛ' hN' hell'
  refine ⟨δ,hδ,?_⟩
  intro ε hε
  obtain ⟨D,hD,he⟩ := hestimate ε hε
  refine ⟨D*(B+V),by positivity,?_⟩
  intro p T hT
  obtain ⟨d⟩ := hdata p
  exact he d.coefficient d.norm_coefficient d.positive d.lower d.upper d.diagonal
    p.flatFunction (p.flatFunction_contDiff hG hB₀) d.trace d.source B V hB.le hV.le
    d.norm_source d.first d.second d.equation T hT

end OAI.Analysis.PDE.Elliptic
