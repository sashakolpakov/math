import OAI.Analysis.PDE.Dirichlet.C2HolderPeriodicSmooth
import OAI.Analysis.PDE.Dirichlet.C2HolderPeriodicDerivativeValue
import OAI.Analysis.PDE.Dirichlet.C2HolderSubtypeDerivative

open Set Module
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {m s : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {Ω K : Set (CoordinateSpace m s)} {hΩK : Ω ⊆ K} {α : ℝ}
  {e : CoordinateSpace m s ≃L[ℝ] P × V} {b : Basis ι ℝ P}

local instance derivativeC2NormedGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance
local instance derivativeC2NormedSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance
local instance derivativeC2Module : Module ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance
local instance derivativeC2BoundedSMul : IsBoundedSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  NormedSpace.toIsBoundedSMul
local instance derivativeC2ContinuousSMul : ContinuousSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  IsBoundedSMul.continuousSMul

omit [Fintype ι] in
/-- Forgetting the periodic codomain after differentiation gives exactly the
ambient derivative applied to the inclusion of the periodic Dirichlet
direction. Both subtype restrictions are accounted for. -/
theorem fderiv_periodicMooreDirichletOperator_coe
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (hα : 0 ≤ α) (slots : Fin s → Q) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u w : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) :
    (fderiv ℝ (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv) u w).val =
      fderiv ℝ (mooreDirichletOperator hα slots) (v + u.val) w.val := by
  let X := OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
  let Y := OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := K) (α := α) e b
  let iX : X →L[ℝ] OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α :=
    (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL
  let iY : Y →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap K ℝ α := (OAI.Analysis.Normed.Function.Holder.latticeHolder (K := K) (α := α) e b).subtypeL
  let F : X → Y := periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv
  have hF : DifferentiableAt ℝ F u :=
    (contDiff_periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv).differentiable
      (by simp) u
  have hout : DifferentiableAt ℝ (mooreDirichletOperator hα slots) (v + u.val) :=
    (contDiff_mooreDirichletOperator hα slots 1).differentiable (by norm_num) _
  exact derivative_commuting_inclusions iX iY F (mooreDirichletOperator hα slots)
    v u w hF hout (fun _ ↦ rfl)

omit [Fintype ι] in
theorem fderiv_periodicMooreDirichletOperator_closed_value
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (hα : 0 ≤ α) (slots : Fin s → Q) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u w : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) (x : K) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value
      (fderiv ℝ (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv) u w).val x =
      OAI.LinearAlgebra.Moore.mooreDifferential m
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α slots (v + u.val)) x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α slots w.val) x) := by
  rw [fderiv_periodicMooreDirichletOperator_coe]
  exact fderiv_mooreDirichletOperator_closed_value hα slots (v + u.val) w.val x

end OAI.Analysis.PDE.Dirichlet
