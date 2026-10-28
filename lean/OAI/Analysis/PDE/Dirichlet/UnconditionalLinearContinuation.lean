import OAI.Analysis.PDE.Dirichlet.UnconditionalLinear
import OAI.Analysis.PDE.Dirichlet.PositiveLattice

open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]

section RegularDomain

variable (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (ψ : CoordinateSpace n 4 → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψp : LatticePeriodic e lat ψ)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hv : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat)
    (hH : ∀ x : {x | r x ≤ 0},
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (v + u.val)) x =
        quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)

include hn hK hbounded hreg hrpos hα1 hψ hψp hψpos hH

omit [FiniteDimensional ℝ P] in
/-- A smooth local inverse for the actual nonlinear periodic Dirichlet map,
with its derivative isomorphism obtained from the proved elliptic solver. -/
theorem periodicMooreDirichlet_localInverse_unconditional :
    let F := periodicMooreDirichletOperator
      (isOpen_lt hr.continuous continuous_const) hclosure
      (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots v hv
    ∃ G : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e lat →
      OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat,
      ContDiffAt ℝ ∞ G (F u) ∧ G (F u) = u ∧
      (∀ᶠ y in 𝓝 (F u), F (G y) = y) ∧
      (∀ᶠ z in 𝓝 u, G (F z) = z) := by
  obtain ⟨L, hL⟩ := exists_periodicMooreDirichlet_derivative_equiv_unconditional
    hn e lat hK hr hrp hbounded hreg hrpos hclosure hα hα1 ψ hψ hψp hψpos v hv u hH
  exact periodicMooreDirichlet_localInverse
    (isOpen_lt hr.continuous continuous_const) hclosure
    (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots v hv u L hL

omit [FiniteDimensional ℝ P] in
/-- Nearby periodic Hölder right-hand sides have actual solutions whose
quaternion Hessian stays positive on the entire closed periodic domain.
Neither an inverse nor an analytic estimate is a premise. -/
theorem periodicMooreDirichlet_positive_continuation_unconditional :
    let F := periodicMooreDirichletOperator
      (isOpen_lt hr.continuous continuous_const) hclosure
      (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots v hv
    ∀ᶠ g in 𝓝 (F u), ∃ w : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat,
      (∀ x : {x | r x ≤ 0}, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value
        (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (v + w.val)) x)).PosDef) ∧ F w = g := by
  obtain ⟨L, hL⟩ := exists_periodicMooreDirichlet_derivative_equiv_unconditional
    hn e lat hK hr hrp hbounded hreg hrpos hclosure hα hα1 ψ hψ hψp hψpos v hv u hH
  have hpos : ∀ x : {x | r x ≤ 0}, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value
      (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (v + u.val)) x)).PosDef := by
    intro x
    rw [hH x]
    exact hψpos x x.property
  exact periodicMooreDirichlet_positive_lattice_continuation
    (isOpen_lt hr.continuous continuous_const) hclosure
    (hrp.comp (fun t ↦ t < 0)) hr.continuous hrp hK hbounded hα.le v hv u hpos L hL

end RegularDomain
end OAI.Analysis.PDE.Dirichlet
