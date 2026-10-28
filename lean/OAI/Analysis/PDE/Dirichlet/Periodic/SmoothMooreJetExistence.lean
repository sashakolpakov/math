import OAI.Analysis.PDE.Dirichlet.SmoothMooreExistence
import OAI.Analysis.PDE.Dirichlet.Periodic.SmoothMooreJet

open Set Module
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
  [Fintype ι]

omit [FiniteDimensional ℝ P] in
/-- Smooth positive periodic Moore coefficients admit an actual solution
in the closed periodic C²,α Dirichlet Banach space. Its value and two
derivatives are the genuine jets of a global C³ function, and the equation
holds on the whole closed domain. No solvability or Hölder bound is assumed. -/
theorem exists_smooth_moore_dirichlet_C2Holder_solution
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r ψ g : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hψ : ContDiff ℝ ∞ ψ) (hψp : LatticePeriodic e lat ψ)
    (hpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (hg : ContDiff ℝ ∞ g) (hgp : LatticePeriodic e lat g)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ u : CoordinateSpace n 4 → ℝ, ContDiff ℝ 3 u ∧ LatticePeriodic e lat u ∧
      (∀ x, r x = 0 → u x = 0) ∧
      ∃ v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α,
        v ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧ ∃ C : ℝ, 0 < C ∧ ‖v‖ ≤ C ∧
          (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value v x = u x) ∧
          (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative v x = fderiv ℝ u x) ∧
          (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative v x =
            fderiv ℝ (fderiv ℝ u) x) ∧
          (∀ x : {x | r x ≤ 0}, OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)
            (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots v) x) = g x) := by
  obtain ⟨u, hu, hup, hu0, hueq⟩ := exists_smooth_moore_dirichlet_solution
    hn e lat hK hr hrp hbounded hreg hψ hψp hpos hg hgp 3 (by norm_num)
  refine ⟨u, hu, hup, hu0, ?_⟩
  exact periodic_moore_C2Holder_jet_of_solution e lat hK (hr.of_le (by norm_num))
    hrp hbounded hreg (hψ.of_le (by norm_num)) hu hup hu0 hg.continuous hueq hα hα1

end OAI.Analysis.PDE.Dirichlet
