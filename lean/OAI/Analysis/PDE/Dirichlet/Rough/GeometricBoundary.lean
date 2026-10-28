import OAI.Analysis.PDE.Dirichlet.Rough.GeometricCurves

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {m n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "X" => EuclideanSpace ℝ (Fin m)
local notation "Y" => CoordinateSpace n 4

/-- The actual geometric curve identity now discharges every tangential
regularity hypothesis of the C²-to-C⁴ Moore boundary bootstrap. -/
theorem HasGeometricSolutionCurves.exists_C4_chart_representative
    [Nontrivial Y] (j : X ≃ₗᵢ[ℝ] Y)
    {e : Y ≃L[ℝ] P × V} {b : Basis ι ℝ P} {r ψ B : Y → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hc : HasGeometricSolutionCurves e b r ψ B hΩD α)
    (hr : ContDiff ℝ 3 r) (hrp : LatticePeriodic e b r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hψ : ContDiff ℝ 2 ψ) (hB : ContDiff ℝ ∞ B)
    (G : X → Y) (P' : Y → X) (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P')
    (load : Y → ℝ) (hl : ContDiff ℝ ∞ load)
    (ℓ : X →L[ℝ] ℝ) (ν : X) (hν : ℓ ν = 1) {R : ℝ} (hR : 0 < R)
    (hGS : MapsTo G ({x | 0 ≤ ℓ x} ∩ ball 0 R) {x | r x ≤ 0})
    (hPG : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R), (fun y ↦ P' (G y)) =ᶠ[𝓝 x] id)
    (hGP : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R), (fun y ↦ G (P' y)) =ᶠ[𝓝 (G x)] id)
    (c : ℝ) (hlevel : ∀ z ∈ ball (0 : X) 1, r (G z) = -c * ℓ z)
    (hpos : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R),
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))).PosDef)
    (he : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R),
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x)) = load (G x)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∃ g : X → ℝ, ContDiff ℝ 4 g ∧
      EqOn g (ψ ∘ G) ({x | 0 ≤ ℓ x} ∩ closedBall 0 ρ) := by
  apply exists_C4_moore_chart_of_parameter_curves (hΩD := hΩD) (α := α) hr hreg hψ hB G P' hG hP load hl
    ℓ ν hν hR hGS hPG hGP _ hpos he
  intro v hv
  have hzero : (0 : X) ∈ {x | 0 ≤ ℓ x} ∩ ball 0 R := by
    simp only [mem_inter_iff,Set.mem_ofPred_eq,map_zero,le_refl,true_and,mem_ball,dist_self]
    exact hR
  obtain ⟨D,hD⟩ := exists_boundary_periodicDomainDeformation j e b r hrp hG hP rfl
    (hPG 0 hzero) ((-c) • ℓ) 0 (by
      intro z hz
      simpa only [zero_add,smul_apply,smul_eq_mul] using hlevel z hz) v
    (by simp only [smul_apply,hv,smul_zero])
  obtain ⟨U,hU,hvalue⟩ := hc D
  obtain ⟨O,hO,hzeroO,hgerm⟩ := translation_curve_germs hGS hvalue hD
  exact ⟨O,hO,hzeroO,U,hU,hgerm⟩

end OAI.Analysis.PDE.Dirichlet
