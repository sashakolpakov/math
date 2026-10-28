import OAI.Analysis.PDE.Dirichlet.Moore.GlobalSchauder
import OAI.Analysis.PDE.Dirichlet.Rough.Moore.Equiv

open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]

omit [FiniteDimensional ℝ P] in
/-- The genuine linearized Moore Dirichlet equation is solvable for arbitrary
periodic Hölder forcing. The uniform Schauder estimate is proved, not an input. -/
theorem exists_C3_moore_dirichlet_solution_unconditional
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
      ∃ v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ‖v‖ ≤ C * ‖f‖ ∧
        v ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
        ∀ x : {x | r x ≤ 0}, OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)
          (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots v) x) =
            OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val x := by
  exact exists_C3_moore_dirichlet_solution_of_uniform_schauder
    hn e lat hK hr hrp hbounded hreg hrpos hα hα1.le
    (uniform_periodic_moore_schauder hn e lat hK r (hr.of_le (by simp))
      hrp hbounded hreg hα hα1) ψ hψ hψp hψpos

omit [FiniteDimensional ℝ P] in
theorem mooreDirichletSolvable_unconditional
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
    MooreDirichletSolvable e lat hΩD α (fun x ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) :=
  mooreDirichletSolvable_of_bounded e lat _
    (exists_C3_moore_dirichlet_solution_unconditional
      hn e lat hK hr hrp hbounded hreg hrpos hα hα1 ψ hψ hψp hψpos)

omit [FiniteDimensional ℝ P] in
/-- The actual derivative of the nonlinear periodic Moore map is a Banach
isomorphism at a positive C³ potential. No inverse or estimate is assumed. -/
theorem exists_periodicMooreDirichlet_derivative_equiv_unconditional
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
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
        quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) :
    ∃ L : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat ≃L[ℝ]
        OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e lat,
      fderiv ℝ (periodicMooreDirichletOperator
        (isOpen_lt hr.continuous continuous_const) hclosure
        (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots v hv) u =
          L.toContinuousLinearMap := by
  exact exists_periodicMooreDirichlet_derivative_equiv_of_uniform_schauder
    hn e lat hK hr hrp hbounded hreg hrpos hclosure hα hα1.le
    (uniform_periodic_moore_schauder hn e lat hK r (hr.of_le (by simp))
      hrp hbounded hreg hα hα1) ψ hψ hψp hψpos v hv u hH

end OAI.Analysis.PDE.Dirichlet
