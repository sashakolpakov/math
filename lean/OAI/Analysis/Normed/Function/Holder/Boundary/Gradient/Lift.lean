import OAI.Analysis.Normed.Function.Holder.Boundary.Gradient.Global
import OAI.Analysis.Normed.Function.Holder.Boundary.Gradient.Interior
import OAI.Analysis.Normed.Function.Holder.Boundary.Gradient.Boundary
import OAI.Analysis.PDE.Weak.PeriodicDirichletSublevel
import OAI.Analysis.PDE.Dirichlet.IndexedHolderApprox

/-! The gradient is a bounded linear map from the actual periodic
Dirichlet C²,α space to the Cα space of covectors. The estimate is derived
from the regular boundary, compact transverse geometry, and stored jets. -/

noncomputable section
open Set Metric Module
open scoped ContDiff
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Elliptic

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "X" => EuclideanSpace ℝ (Fin (n*4))
local instance gradientLiftFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance gradientLiftFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

theorem physical_first_jet_local_holder
    (hn : 0 < n) {r : E → ℝ} (hr : ContDiff ℝ ∞ r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0})
    {α : ℝ} (hα1 : α ≤ 1) :
    ∀ a, r a ≤ 0 → ∃ ρ > 0, ∃ C > 0,
      ∀ U : C2Holder (F := ℝ) hΩK α,
        ∀ x ∈ closedBall a ρ, r x ≤ 0 → ∀ y ∈ closedBall a ρ, r y ≤ 0 →
        ‖boundedZeroExtension (C2Holder.firstDerivative U) x-boundedZeroExtension (C2Holder.firstDerivative U) y‖ ≤
          C*‖U‖*dist x y^α := by
    intro a ha
    rcases lt_or_eq_of_le ha with hneg | hzero
    · exact C2Holder.interior_first_jet_holder_bound hΩK (isOpen_lt hr.continuous continuous_const) hneg hα1
    · let e₀ : X ≃ₗᵢ[ℝ] E := (OAI.Analysis.PDE.Dirichlet.flattenFourSlots n).symm
      let k : Fin (n*4) := ⟨0,by omega⟩
      exact C2Holder.boundary_first_jet_holder_bound e₀ k hr hΩK hzero (hreg a hzero) hα1
theorem exists_lattice_gradient_holder_clm
    (hn : 0 < n) (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r : E → ℝ} (hr : ContDiff ℝ ∞ r)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0})
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ L : C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b →L[ℝ]
        HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α,
      ∀ U, OAI.Analysis.Normed.Function.Holder.HolderMap.value (L U) = C2Holder.firstDerivative U.val := by
  have hKΩ : {x | r x ≤ 0} ⊆ closure {x | r x < 0} := by
    rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r (hr.of_le (by simp)) hreg]
  exact C2Holder.exists_lattice_gradient_holder_clm_of_local e b hK hr.continuous
    hrp hbounded hΩK hKΩ hα (C2Holder.physical_first_jet_local_holder hn hr hreg hΩK hα1)

end OAI.Analysis.Normed.Function.Holder.C2Holder
