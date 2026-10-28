import OAI.Analysis.PDE.Dirichlet.C2HolderPeriodicOperator
import OAI.Analysis.Normed.Operator.ClosedSubspace.Smooth

open Set Module
open scoped ContDiff
noncomputable section

namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {m s : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {Ω K : Set (CoordinateSpace m s)} {hΩK : Ω ⊆ K} {α : ℝ}
  {e : CoordinateSpace m s ≃L[ℝ] P × V} {b : Basis ι ℝ P}

local instance periodicC2NormedGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  inferInstance
local instance periodicC2NormedSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  inferInstance
local instance periodicC2Module : Module ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance
local instance periodicC2BoundedSMul : IsBoundedSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  NormedSpace.toIsBoundedSMul
local instance periodicC2ContinuousSMul : ContinuousSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  IsBoundedSMul.continuousSMul

omit [Fintype ι] in
/-- The actual periodic nonlinear operator is smooth into the closed periodic
Hölder space, not merely after forgetting periodicity. -/
theorem contDiff_periodicMooreDirichletOperator
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (hα : 0 ≤ α) (slots : Fin s → Q) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v))) :
    ContDiff ℝ ∞ (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv) := by
  apply OAI.Analysis.Normed.Operator.ClosedSubspace.contDiff_infty_of_isometry
    (OAI.Analysis.Normed.Function.Holder.latticeHolder (K := K) (α := α) e b).subtypeₗᵢ
  change ContDiff ℝ ∞ (fun u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace
    (hΩK := hΩK) (α := α) e b ↦ mooreDirichletOperator hα slots (v + u.val))
  let inclusion : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b →L[ℝ]
      OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α :=
    (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL
  have hin : ContDiff ℝ ∞ (fun u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace
      (hΩK := hΩK) (α := α) e b ↦ v + inclusion u) :=
    contDiff_const.add inclusion.contDiff
  exact (contDiff_mooreDirichletOperator hα slots ∞).comp hin

omit [Fintype ι] in
theorem contDiff_periodicMooreDirichletOperator_nat
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (hα : 0 ≤ α) (slots : Fin s → Q) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v))) (k : ℕ) :
    ContDiff ℝ k (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv) :=
  (contDiff_periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv).of_le
    (by simp)

end OAI.Analysis.PDE.Dirichlet
