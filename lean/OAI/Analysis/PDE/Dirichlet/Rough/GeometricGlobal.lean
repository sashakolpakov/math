import OAI.Analysis.PDE.Dirichlet.Rough.GeometricBoundaryPoint
import OAI.Analysis.PDE.Dirichlet.Rough.RegularityGlobal

noncomputable section
open Set Module
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "Y" => CoordinateSpace n 4

/-- The actual geometric Banach curves give a global periodic C⁴
representative. Both classical derivative fields are preserved on the
entire closed domain, not merely almost everywhere or in the interior. -/
theorem HasGeometricSolutionCurves.exists_periodic_C4_representative
    [Nontrivial Y] (hn : 1 ≤ n)
    {e : Y ≃L[ℝ] P × V} {b : Basis ι ℝ P} {K : Set V} (hK : IsCompact K)
    {r ψ B : Y → ℝ} {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hc : HasGeometricSolutionCurves e b r ψ B hΩD α)
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hψ : ContDiff ℝ 2 ψ) (hψp : LatticePeriodic e b ψ) (hB : ContDiff ℝ ∞ B)
    (load : Y → ℝ) (hl : ContDiff ℝ ∞ load)
    (hpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (he : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = load x) :
    ∃ g : Y → ℝ, ContDiff ℝ 4 g ∧ LatticePeriodic e b g ∧
      (∀ x, r x ≤ 0 → g x = ψ x) ∧
      (∀ x, r x ≤ 0 → fderiv ℝ g x = fderiv ℝ ψ x) ∧
      (∀ x, r x ≤ 0 → fderiv ℝ (fderiv ℝ g) x = fderiv ℝ (fderiv ℝ ψ) x) := by
  obtain ⟨g,hg,hgp,hgeq⟩ := exists_periodic_representative_of_local_regularities
    e b hK hr.continuous hrp hbounded ψ hψp
    (fun x hx ↦ hc.contDiffAt_four_interior hr.continuous hrp hψ (hB.of_le (by simp)) hx)
    (by
      intro a ha
      obtain ⟨O,hO,haO,v,hv,heq⟩ := hc.exists_C4_boundary_representative hn
        hr hrp hreg hψ hB load hl hpos he ha
      exact ⟨O,hO,haO,v,hv.contDiffOn,heq⟩)
  have hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0} := by
    rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r (hr.of_le (by simp)) hreg]
  obtain ⟨hfirst,hsecond⟩ := first_second_eqOn_of_eqOn_dense_interior
    (isOpen_lt hr.continuous continuous_const) hΩD hclosure
    (hg.of_le (by norm_num)) hψ (fun x hx ↦ hgeq x hx)
  exact ⟨g,hg,hgp,hgeq,(fun x hx ↦ hfirst hx),(fun x hx ↦ hsecond hx)⟩

end OAI.Analysis.PDE.Dirichlet
