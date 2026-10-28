import OAI.Analysis.Normed.Function.Holder.Moore
import OAI.Analysis.PDE.Schauder.Calculus.SliceDerivative

open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {X Y : Type*} [MetricSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ} {α : ℝ}
local notation "A" => OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α
local instance fieldMatrixGroup : NormedAddCommGroup (Matrix (Fin n) (Fin n) (Quaternion ℝ)) := inferInstance
local instance fieldMatrixSpace : NormedSpace ℝ (Matrix (Fin n) (Fin n) (Quaternion ℝ)) := inferInstance
local instance fieldHolderGroup : NormedAddCommGroup A := inferInstance
local instance fieldHolderSpace : NormedSpace ℝ A := inferInstance
local instance fieldRealHolderGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α) := inferInstance
local instance fieldRealHolderSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α) := inferInstance

theorem differentiableAt_mooreDetField (hα : 0 ≤ α) (a : A) :
    DifferentiableAt ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα n) a :=
  (OAI.Analysis.Normed.Function.Holder.contDiff_mooreDetField hα n 1).differentiable (by norm_num) a

theorem hasFDerivAt_mooreDetField_affine (hα : 0 ≤ α)
    (L : Y →L[ℝ] A) (a : A) (c : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α) (y : Y) :
    HasFDerivAt (fun z => OAI.Analysis.Normed.Function.Holder.mooreDetField hα n (a+L z)-c)
      ((fderiv ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα n) (a+L y)).comp L) y :=
  hasFDerivAt_affine_map_sub L (OAI.Analysis.Normed.Function.Holder.mooreDetField hα n) a c y
    (differentiableAt_mooreDetField hα (a+L y))

theorem hasFDerivAt_mooreDetField_comp (hα : 0 ≤ α)
    (L : Y →L[ℝ] A) (y : Y) :
    HasFDerivAt (fun z => OAI.Analysis.Normed.Function.Holder.mooreDetField hα n (L z))
      ((fderiv ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα n) (L y)).comp L) y :=
  (differentiableAt_mooreDetField hα (L y)).hasFDerivAt.comp y L.hasFDerivAt

end OAI.Analysis.PDE.Schauder
