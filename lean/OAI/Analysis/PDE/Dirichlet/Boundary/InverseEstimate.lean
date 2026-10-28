import OAI.Analysis.PDE.Dirichlet.Boundary.InverseOperator
import OAI.Analysis.PDE.Dirichlet.ClassicalLinearIdentification
import OAI.Analysis.PDE.Dirichlet.Periodic.MooreBarrier
import OAI.Analysis.PDE.Weak.PeriodicDirichletSublevel

noncomputable section
open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => CoordinateSpace n 4
local instance inverseEstimateFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance inverseEstimateFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance inverseEstimateSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseEstimateSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseEstimateC2Group {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance inverseEstimateC2Space {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance

def HasMooreSolutionBound {Ω D : Set E} (hΩD : Ω ⊆ D) {α : ℝ}
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) (ψ : E → ℝ)
    (C : ℝ) (f : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat) : Prop :=
  ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ‖U‖ ≤ C*‖f‖ ∧
    U ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
    ∀ x : D, OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots U) x) =
        OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val x

omit [FiniteDimensional ℝ P] in
theorem moore_solution_estimate_of_restricted_bound
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) (C : ℝ)
    (hbound : ∀ u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat,
      ‖u‖ ≤ C*‖restrictedMooreDerivative hΩD hα.le e lat g u‖)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψp : LatticePeriodic e lat ψ)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (hfield : ∀ x : {x | r x ≤ 0},
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots g) x =
        quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)
    (f : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e lat) :
    HasMooreSolutionBound hΩD e lat ψ C f := by
  obtain ⟨_,_,hsolve⟩ := exists_C3_moore_dirichlet_solution_unconditional
    (hΩD := hΩD) hn e lat hK hr hrp hbounded hreg hrpos hα hα1 ψ hψ hψp hψpos
  obtain ⟨U,_,hU,hUL⟩ := hsolve f
  have heq : restrictedMooreDerivative hΩD hα.le e lat g ⟨U,hU⟩ = f.val := by
    apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
    apply BoundedContinuousFunction.ext
    intro x
    change OAI.Analysis.Normed.Function.Holder.HolderMap.value (fderiv ℝ (mooreDirichletOperator hα.le OAI.Analysis.Calculus.Quaternion.fourSlots) g U) x = _
    exact (fderiv_mooreDirichletOperator_closed_value hα.le OAI.Analysis.Calculus.Quaternion.fourSlots g U x).trans
      ((congrArg (fun A => OAI.LinearAlgebra.Moore.mooreDifferential n A
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots U) x)) (hfield x)).trans (hUL x))
  have hnorm : ‖U‖ ≤ C*‖f‖ := calc
    ‖U‖ ≤ C*‖restrictedMooreDerivative hΩD hα.le e lat g ⟨U,hU⟩‖ := hbound ⟨U,hU⟩
    _ = C*‖f‖ := congrArg (fun y => C*‖y‖) heq
  exact ⟨U,hnorm,hU,hUL⟩

end OAI.Analysis.PDE.Dirichlet
