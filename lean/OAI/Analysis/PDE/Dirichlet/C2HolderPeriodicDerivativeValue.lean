import OAI.Analysis.PDE.Dirichlet.C2HolderNonlinear

open Set
open scoped Matrix.Norms.Elementwise ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {m s : ℕ} {Ω K : Set (CoordinateSpace m s)} {hΩK : Ω ⊆ K} {α : ℝ}

local instance closedC2NormedGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance
local instance closedC2NormedSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance
local instance closedC2Module : Module ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance
local instance closedC2BoundedSMul : IsBoundedSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  NormedSpace.toIsBoundedSMul
local instance closedC2ContinuousSMul : ContinuousSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  IsBoundedSMul.continuousSMul

theorem fderiv_mooreDirichletOperator_eq
    (hα : 0 ≤ α) (slots : Fin s → Q) (f : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :
    fderiv ℝ (mooreDirichletOperator hα slots) f =
      (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα m) (quaternionHessianField hΩK α slots f)).comp
        (quaternionHessianField hΩK α slots) := by
  let J := quaternionHessianField hΩK α slots
  have hF := ((OAI.Analysis.Normed.Function.Holder.contDiff_mooreDetField (X := K) hα m 1).differentiable
    (by norm_num) (J f)).hasFDerivAt
  have hchain : HasFDerivAt (mooreDirichletOperator hα slots)
      ((fderiv ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα m) (J f)).comp J) f :=
    hF.comp f J.hasFDerivAt
  exact hchain.fderiv

theorem fderiv_mooreDirichletOperator_closed_value
    (hα : 0 ≤ α) (slots : Fin s → Q) (f w : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (x : K) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (fderiv ℝ (mooreDirichletOperator hα slots) f w) x =
      OAI.LinearAlgebra.Moore.mooreDifferential m
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α slots f) x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α slots w) x) := by
  rw [fderiv_mooreDirichletOperator_eq, ContinuousLinearMap.comp_apply]
  exact OAI.Analysis.Normed.Function.Holder.fderiv_mooreDetField_value hα m
    (quaternionHessianField hΩK α slots f) (quaternionHessianField hΩK α slots w) x

end OAI.Analysis.PDE.Dirichlet
