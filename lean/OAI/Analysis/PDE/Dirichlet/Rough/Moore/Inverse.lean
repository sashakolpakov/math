import OAI.Analysis.PDE.Dirichlet.Rough.Moore.Solvability
import OAI.Analysis.PDE.Dirichlet.Periodic.DerivativePositive
import OAI.Analysis.PDE.Dirichlet.C2HolderImplicit

open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance inverseC2NormedGroup {Ω D : Set (CoordinateSpace n 4)}
    {hΩD : Ω ⊆ D} {α : ℝ} : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance inverseC2NormedSpace {Ω D : Set (CoordinateSpace n 4)}
    {hΩD : Ω ⊆ D} {α : ℝ} : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance inverseC2Module {Ω D : Set (CoordinateSpace n 4)}
    {hΩD : Ω ⊆ D} {α : ℝ} : Module ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance inverseC2BoundedSMul {Ω D : Set (CoordinateSpace n 4)}
    {hΩD : Ω ⊆ D} {α : ℝ} : IsBoundedSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) :=
  NormedSpace.toIsBoundedSMul
local instance inverseC2ContinuousSMul {Ω D : Set (CoordinateSpace n 4)}
    {hΩD : Ω ⊆ D} {α : ℝ} : ContinuousSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) :=
  IsBoundedSMul.continuousSMul

omit [Fintype ι] in
theorem fderiv_periodicMooreDirichletOperator_surjective_of_solvability
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {Ω D : Set (CoordinateSpace n 4)} {hΩD : Ω ⊆ D} {α : ℝ}
    (hΩ : IsOpen Ω) (hclosure : D ⊆ closure Ω)
    (hΩp : LatticePeriodic e lat (fun x ↦ x ∈ Ω))
    (hDp : LatticePeriodic e lat (fun x ↦ x ∈ D))
    (hα : 0 ≤ α) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hv : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat)
    (hsolve : MooreDirichletSolvable e lat hΩD α
      (fun x ↦ OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (v + u.val)) x)) :
    Function.Surjective (fderiv ℝ
      (periodicMooreDirichletOperator hΩ hclosure hΩp hDp hα OAI.Analysis.Calculus.Quaternion.fourSlots v hv) u) := by
  intro f
  obtain ⟨w, hw, hwe⟩ := hsolve f
  refine ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
  ext x
  rw [fderiv_periodicMooreDirichletOperator_closed_value]
  exact hwe x

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]

omit [FiniteDimensional ℝ P] in
/-- The proved rough-coefficient solver gives surjectivity of the actual
periodic derivative, including both its domain and codomain restrictions. -/
theorem fderiv_periodicMooreDirichletOperator_surjective_of_uniform_schauder
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hschauder : UniformPeriodicMooreSchauderEstimate e lat hΩD α)
    (ψ : CoordinateSpace n 4 → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψp : LatticePeriodic e lat ψ)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hv : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat)
    (hH : ∀ x : {x | r x ≤ 0},
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (v + u.val)) x =
        quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) :
    Function.Surjective (fderiv ℝ (periodicMooreDirichletOperator
      (isOpen_lt hr.continuous continuous_const) hclosure
      (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots v hv) u) := by
  apply fderiv_periodicMooreDirichletOperator_surjective_of_solvability
    e lat (isOpen_lt hr.continuous continuous_const) hclosure
    (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le v hv u
  exact (mooreDirichletSolvable_of_uniform_schauder
    hn e lat hK hr hrp hbounded hreg hrpos hα hα1 hschauder ψ hψ hψp hψpos).congr hH

omit [FiniteDimensional ℝ P] in
/-- The actual periodic derivative is bijective at a C³ positive base,
conditional only on the uniform a priori Schauder estimate. -/
theorem fderiv_periodicMooreDirichletOperator_bijective_of_uniform_schauder
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hschauder : UniformPeriodicMooreSchauderEstimate e lat hΩD α)
    (ψ : CoordinateSpace n 4 → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψp : LatticePeriodic e lat ψ)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hv : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat)
    (hH : ∀ x : {x | r x ≤ 0},
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (v + u.val)) x =
        quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) :
    Function.Bijective (fderiv ℝ (periodicMooreDirichletOperator
      (isOpen_lt hr.continuous continuous_const) hclosure
      (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots v hv) u) := by
  refine ⟨?_, fderiv_periodicMooreDirichletOperator_surjective_of_uniform_schauder
    hn e lat hK hr hrp hbounded hreg hrpos hclosure hα hα1 hschauder ψ hψ hψp hψpos v hv u hH⟩
  apply fderiv_periodicMooreDirichletOperator_injective hn e lat hK
    (hr.of_le (by simp)) hrp hbounded hclosure
    (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le v hv u
  · intro x hx
    rw [hH]
    exact hψpos x hx.le
  · intro x hx
    exact hrpos x hx.le

end OAI.Analysis.PDE.Dirichlet
