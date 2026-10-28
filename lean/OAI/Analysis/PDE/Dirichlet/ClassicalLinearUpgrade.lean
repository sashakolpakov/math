import OAI.Analysis.PDE.Dirichlet.ClassicalLinearIdentification
import OAI.Analysis.PDE.Dirichlet.UnconditionalLinear
import OAI.Analysis.PDE.Dirichlet.Periodic.MooreBarrier
import OAI.Analysis.PDE.Weak.PeriodicDirichletSublevel

/-! A classical C² solution inherits the quantitative closed C²,α estimate
from the genuine Dirichlet inverse. This does not assume Hölder continuity
of its second derivatives. -/

noncomputable section
open Set Filter Module
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]

omit [FiniteDimensional ℝ P] in
theorem exists_C2Holder_classical_moore_solution
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (ψ : CoordinateSpace n 4 → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψp : LatticePeriodic e lat ψ)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e lat,
      ∀ w : CoordinateSpace n 4 → ℝ, ContDiff ℝ 2 w → LatticePeriodic e lat w →
        (∀ x, r x = 0 → w x = 0) →
        (∀ x (hx : r x < 0), mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) w x =
          OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val ⟨x, hΩD hx⟩) →
      ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α,
        ‖U‖ ≤ C * ‖f‖ ∧ U ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
        (∀ x : {x | r x ≤ 0}, w x = OAI.Analysis.Normed.Function.Holder.C2Holder.value U x) ∧
        (∀ x : {x | r x ≤ 0}, fderiv ℝ w x = OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x) ∧
        (∀ x : {x | r x ≤ 0},
          fderiv ℝ (fderiv ℝ w) x = OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x) := by
  obtain ⟨C, hC, hsolve⟩ := exists_C3_moore_dirichlet_solution_unconditional
    (hΩD := hΩD) hn e lat hK hr hrp hbounded hreg hrpos hα hα1 ψ hψ hψp hψpos
  have hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0} := by
    rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r
      (hr.of_le (by simp)) hreg]
  obtain ⟨c, hc, hclower⟩ := periodic_moore_defining_positive_lower hn e lat hK
    (hr.of_le (by simp)) hrp hbounded (hψ.of_le (by norm_num)) hψp hrpos hψpos
  refine ⟨C, hC, ?_⟩
  intro f w hw hwp hwzero hwL
  obtain ⟨U, hUnorm, hU, hUL⟩ := hsolve f
  refine ⟨U, hUnorm, hU, ?_⟩
  apply moore_classical_eq_banach_jets e lat hK (hr.of_le (by simp)) hrp hbounded
    hclosure (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) (fun x hx ↦ hψpos x hx.le)
    (fun x hx ↦ hc.trans_le (hclower x hx.le)) U hU w hw hwp hwzero
  intro x hx
  exact (hwL x hx).trans (hUL ⟨x, hΩD hx⟩).symm

end OAI.Analysis.PDE.Dirichlet
