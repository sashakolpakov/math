import OAI.Analysis.PDE.Dirichlet.C2HolderQuaternion
import OAI.Analysis.Normed.Function.Holder.MooreDerivative

open Set
open scoped Matrix.Norms.Elementwise ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {m s : ℕ} {Ω K : Set (CoordinateSpace m s)} {hΩK : Ω ⊆ K} {α : ℝ}

local instance nonlinearC2NormedGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  inferInstance
local instance nonlinearC2NormedSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  inferInstance
local instance nonlinearC2Module : Module ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance
local instance nonlinearC2BoundedSMul : IsBoundedSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  NormedSpace.toIsBoundedSMul
local instance nonlinearC2ContinuousSMul : ContinuousSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :=
  IsBoundedSMul.continuousSMul

/-- The actual quaternionic Monge–Ampère map on the complete Hölder space. -/
def mooreDirichletOperator (hα : 0 ≤ α) (e : Fin s → Q)
    (f : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) : OAI.Analysis.Normed.Function.Holder.HolderMap K ℝ α :=
  OAI.Analysis.Normed.Function.Holder.mooreDetField hα m (quaternionHessianField hΩK α e f)

theorem contDiff_mooreDirichletOperator (hα : 0 ≤ α) (e : Fin s → Q) (k : ℕ∞ω) :
    ContDiff ℝ k (mooreDirichletOperator (hΩK := hΩK) hα e) :=
  (OAI.Analysis.Normed.Function.Holder.contDiff_mooreDetField hα m k).comp (quaternionHessianField hΩK α e).contDiff

theorem mooreDirichletOperator_eq (hΩ : IsOpen Ω) (hα : 0 ≤ α) (e : Fin s → Q)
    (f : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) {x : CoordinateSpace m s} (hx : x ∈ Ω) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (mooreDirichletOperator hα e f) ⟨x, hΩK hx⟩ =
      OAI.LinearAlgebra.Moore.mooreDet m (quaternionHessian e (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value f)) x) := by
  rw [mooreDirichletOperator, OAI.Analysis.Normed.Function.Holder.value_mooreDetField, quaternionHessianField_eq hΩ hΩK α e f hx]

theorem fderiv_mooreDirichletOperator_value (hΩ : IsOpen Ω) (hα : 0 ≤ α)
    (e : Fin s → Q) (f w : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    {x : CoordinateSpace m s} (hx : x ∈ Ω) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (fderiv ℝ (mooreDirichletOperator hα e) f w) ⟨x, hΩK hx⟩ =
      OAI.LinearAlgebra.Moore.mooreDifferential m
        (quaternionHessian e (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value f)) x)
        (quaternionHessian e (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value w)) x) := by
  let J := quaternionHessianField hΩK α e
  have hF := ((OAI.Analysis.Normed.Function.Holder.contDiff_mooreDetField (X := K) hα m 1).differentiable
    (by norm_num) (J f)).hasFDerivAt
  have hchain : HasFDerivAt (mooreDirichletOperator hα e)
      ((fderiv ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα m) (J f)).comp J) f :=
    hF.comp f J.hasFDerivAt
  have hEq : fderiv ℝ (mooreDirichletOperator hα e) f =
      (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα m) (J f)).comp J := hchain.fderiv
  rw [hEq, ContinuousLinearMap.comp_apply, OAI.Analysis.Normed.Function.Holder.fderiv_mooreDetField_value]
  dsimp only [J]
  rw [quaternionHessianField_eq hΩ hΩK α e f hx, quaternionHessianField_eq hΩ hΩK α e w hx]

/-- Adding the fixed background and restricting to zero-boundary perturbations
preserves smoothness in the Dirichlet Hölder Banach space. -/
theorem contDiff_background_dirichlet (hα : 0 ≤ α) (e : Fin s → Q)
    (b : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (k : ℕ∞ω) :
    ContDiff ℝ k (fun u : OAI.Analysis.Normed.Function.Holder.C2Holder.DirichletSpace (F := ℝ) hΩK α ↦
      mooreDirichletOperator hα e (b + u.val)) := by
  let inclusion : OAI.Analysis.Normed.Function.Holder.C2Holder.DirichletSpace (F := ℝ) hΩK α →L[ℝ] OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α :=
    (OAI.Analysis.Normed.Function.Holder.C2Holder.zeroTrace (F := ℝ) (hΩK := hΩK) (α := α)).subtypeL
  have hin : ContDiff ℝ k (fun u : OAI.Analysis.Normed.Function.Holder.C2Holder.DirichletSpace (F := ℝ) hΩK α ↦ b + inclusion u) :=
    contDiff_const.add inclusion.contDiff
  exact (contDiff_mooreDirichletOperator hα e k).comp hin

end OAI.Analysis.PDE.Dirichlet
