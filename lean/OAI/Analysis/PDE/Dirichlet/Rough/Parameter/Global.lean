import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.BoundaryPoint
import OAI.Analysis.PDE.Dirichlet.Rough.RegularityInfinity

noncomputable section
open Set Module
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "X" => EuclideanSpace ℝ (Fin (n*4))
local notation "Y" => CoordinateSpace n 4

/-- Actual geometric solution families imply a single global smooth
periodic representative preserving the whole closed-domain two-jet. -/
theorem exists_smooth_periodic_representative_of_parameter_families
    [Nontrivial Y] (hn : 1 ≤ n)
    {e : Y ≃L[ℝ] P × V} {b : Basis ι ℝ P} {K : Set V} (hK : IsCompact K)
    {r ψ B : Y → ℝ} {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hci : ParameterDeformation.HasGeometricSolutionFamilies (Z := Y) e b r ψ B hΩD α)
    (hct : ∀ k : Fin (n*4), ParameterDeformation.HasGeometricSolutionFamilies
      (Z := (EuclideanSpace.proj k : X →L[ℝ] ℝ).ker) e b r ψ B hΩD α)
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hψ : ContDiff ℝ 2 ψ) (hψp : LatticePeriodic e b ψ) (hB : ContDiff ℝ ∞ B)
    (load : Y → ℝ) (hl : ContDiff ℝ ∞ load)
    (hpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (he : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = load x) :
    ∃ g : Y → ℝ, ContDiff ℝ ∞ g ∧ LatticePeriodic e b g ∧
      (∀ x, r x ≤ 0 → g x = ψ x) ∧
      (∀ x, r x ≤ 0 → fderiv ℝ g x = fderiv ℝ ψ x) ∧
      (∀ x, r x ≤ 0 → fderiv ℝ (fderiv ℝ g) x = fderiv ℝ (fderiv ℝ ψ) x) := by
  have hi : ∀ x, r x < 0 → ContDiffAt ℝ ∞ ψ x :=
    fun x hx ↦ hci.contDiffAt_interior hr.continuous hrp hB hx
  apply exists_smooth_periodic_representative_with_jets e b hK (hr.of_le (by simp))
    hrp hbounded hreg ψ hψ hψp hi
  intro a ha
  obtain ⟨O,hO,haO,g,hg,heq⟩ := ParameterDeformation.exists_smooth_boundary_representative_of_parameter_families
    hn hct hi hr hrp hreg hψ hB load hl hpos he ha
  exact ⟨O,hO,haO,g,hg.contDiffOn,heq⟩

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
