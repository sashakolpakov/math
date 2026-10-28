import OAI.Analysis.PDE.Dirichlet.C2HolderPeriodicDerivative
import OAI.Analysis.PDE.Dirichlet.Linear.BanachUniqueness
import OAI.LinearAlgebra.Moore.Monotone

open Set Module
open scoped ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance injectiveC2NormedGroup {Ω K : Set (CoordinateSpace n 4)}
    {hΩK : Ω ⊆ K} {α : ℝ} : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance
local instance injectiveC2NormedSpace {Ω K : Set (CoordinateSpace n 4)}
    {hΩK : Ω ⊆ K} {α : ℝ} : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance
local instance injectiveC2Module {Ω K : Set (CoordinateSpace n 4)}
    {hΩK : Ω ⊆ K} {α : ℝ} : Module ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance
local instance injectiveC2BoundedSMul {Ω K : Set (CoordinateSpace n 4)}
    {hΩK : Ω ⊆ K} {α : ℝ} : IsBoundedSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  NormedSpace.toIsBoundedSMul
local instance injectiveC2ContinuousSMul {Ω K : Set (CoordinateSpace n 4)}
    {hΩK : Ω ⊆ K} {α : ℝ} : ContinuousSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  IsBoundedSMul.continuousSMul

theorem periodic_linearMap_injective_of_barrier
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hrper : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) Q)
    (hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hrL : ∀ x, r x < 0 → 0 < mooreLinearization A r x)
    {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (L : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e lat →L[ℝ] Z)
    (hL : ∀ w, L w = 0 → ∀ x : {x | r x ≤ 0},
      OAI.LinearAlgebra.Moore.mooreDifferential n (A x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots w.val) x) = 0) :
    Function.Injective L := by
  have hker (w) (hw : L w = 0) : w = 0 := by
    apply Subtype.ext
    exact moore_linearized_banach_eq_zero e lat hC hr hrper hbounded hclosure
      A hA hrL w.val w.property (hL w hw)
  intro w z hwz
  apply sub_eq_zero.mp
  apply hker (w - z)
  rw [map_sub, hwz, sub_self]

/-- The actual Fréchet derivative of the periodic nonlinear map has trivial
kernel at a positive base admitting the defining-function barrier. -/
theorem fderiv_periodicMooreDirichletOperator_injective_of_barrier
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hrper : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hΩper : LatticePeriodic e lat (fun x ↦ r x < 0))
    (hKper : LatticePeriodic e lat (fun x ↦ r x ≤ 0))
    (hα : 0 ≤ α) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e lat)
    (hpos : ∀ x (hx : r x < 0), (OAI.LinearAlgebra.Moore.complexify
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (v + u.val)) ⟨x, hΩK hx⟩)).PosDef)
    (hbarrier : ∀ x (hx : r x < 0), 0 < OAI.LinearAlgebra.Moore.mooreDifferential n
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (v + u.val)) ⟨x, hΩK hx⟩)
      (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)) :
    Function.Injective (fderiv ℝ (periodicMooreDirichletOperator
      (isOpen_lt hr.continuous continuous_const) hclosure hΩper hKper hα OAI.Analysis.Calculus.Quaternion.fourSlots v hv) u) := by
  let hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  let F := periodicMooreDirichletOperator hΩ hclosure hΩper hKper hα OAI.Analysis.Calculus.Quaternion.fourSlots v hv
  let A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) Q :=
    OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (v + u.val)))
  have hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef := by
    intro x hx
    dsimp [A]
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ (hΩK hx)]
    exact hpos x hx
  have hrL : ∀ x, r x < 0 → 0 < mooreLinearization A r x := by
    intro x hx
    change 0 < OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)
    dsimp [A]
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ (hΩK hx)]
    exact hbarrier x hx
  change Function.Injective (fderiv ℝ F u)
  refine periodic_linearMap_injective_of_barrier e lat hC hr hrper hbounded hclosure
    A hA hrL (hΩK := hΩK) (α := α) (fderiv ℝ F u) ?_
  intro w hw x
  dsimp [A]
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property]
  have heq := fderiv_periodicMooreDirichletOperator_closed_value
    hΩ hclosure hΩper hKper hα OAI.Analysis.Calculus.Quaternion.fourSlots v hv u w x
  have heq0 : OAI.Analysis.Normed.Function.Holder.HolderMap.value (fderiv ℝ F u w).val x = 0 := by
    rw [hw]
    rfl
  exact heq.symm.trans heq0

end OAI.Analysis.PDE.Dirichlet
