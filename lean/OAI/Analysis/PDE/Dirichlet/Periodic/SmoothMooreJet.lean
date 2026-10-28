import OAI.Analysis.PDE.Dirichlet.Periodic.SmoothJetEquation

open Set Module
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- An actual smooth periodic solution supplies a closed-domain Banach jet
with its exact derivatives and the actual closed-domain Moore equation. -/
theorem periodic_moore_C2Holder_jet_of_solution
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r ψ u g : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 1 r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hψ : ContDiff ℝ 2 ψ) (hu : ContDiff ℝ 3 u)
    (hup : LatticePeriodic e lat u) (hu0 : ∀ x, r x = 0 → u x = 0)
    (hg : Continuous g)
    (hueq : ∀ x, r x < 0 → mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) u x = g x)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α,
      v ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧ ∃ C : ℝ, 0 < C ∧ ‖v‖ ≤ C ∧
        (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value v x = u x) ∧
        (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative v x = fderiv ℝ u x) ∧
        (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative v x = fderiv ℝ (fderiv ℝ u) x) ∧
        (∀ x : {x | r x ≤ 0}, OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)
          (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots v) x) = g x) := by
  obtain ⟨v, C, hC, hvnorm, hv0, hv1, hv2, hv⟩ :=
    exists_periodic_dirichlet_C2Holder_jet e lat hK hr.continuous hrp hbounded
      (hΩD := hΩD) u hu hup hu0 hα hα1
  refine ⟨v, hv, C, hC, hvnorm, hv0, hv1, hv2, ?_⟩
  exact mooreLinearization_C2Holder_on_closed_sublevel hr hreg hψ
    (hu.of_le (by norm_num)) hg hueq v hv2

end OAI.Analysis.PDE.Dirichlet
