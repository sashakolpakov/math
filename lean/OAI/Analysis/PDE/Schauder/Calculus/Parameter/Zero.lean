import OAI.Analysis.PDE.Schauder.Calculus.Parameter.Hessian
import OAI.Analysis.PDE.Schauder.Calculus.MooreFieldDerivative

open Set Module
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {U : Set Z}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "D" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
attribute [local instance] latticeJetsDualGroup latticeJetsDualSpace
  latticeJetsSecondGroup latticeJetsSecondSpace
local instance parameterZeroEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance parameterZeroEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance parameterZeroMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance parameterZeroMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem transformedHessianField_eq_of_identity
    {Y : Type*} [MetricSpace Y] (hα : 0 ≤ α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap Y (E →L[ℝ] E) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap Y (E →L[ℝ] E →L[ℝ] E) α)
    (p : OAI.Analysis.Normed.Function.Holder.HolderMap Y (E →L[ℝ] ℝ) α)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap Y (E →L[ℝ] E →L[ℝ] ℝ) α)
    (hJ : J = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E))
    (hT : T = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0) :
    transformedHessianField hα J T p B = B := by
  rw [hJ,hT,transformedHessianField_identity]

omit [Fintype ι] in
theorem ParameterJetFields.hessianField_base
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α)
    (z₀ : Z) (hJ : C.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E))
    (hK : C.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0) (v : D) :
    C.hessianField J hα (z₀,v) =
      OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots) (C.background z₀ + J.second v) := by
  exact congrArg (fun H => OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)
    (C.background z₀ + H))
    (transformedHessianField_eq_of_identity hα _ _ (J.first v) (J.second v) hJ hK)

omit [Fintype ι] in
theorem ParameterJetFields.mooreOperator_base
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α)
    (z₀ : Z) (hJ : C.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E))
    (hK : C.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0) (v : D) :
    C.mooreOperator J hα (z₀,v) =
      OAI.Analysis.Normed.Function.Holder.mooreDetField hα n (OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)
        (C.background z₀ + J.second v)) - C.source z₀ := by
  exact congrArg (fun H => OAI.Analysis.Normed.Function.Holder.mooreDetField hα n
    (OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots) (C.background z₀ + H)) - C.source z₀)
    (transformedHessianField_eq_of_identity hα _ _ (J.first v) (J.second v) hJ hK)

omit [Fintype ι] in
theorem ParameterJetFields.mooreOperator_base_affine
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α)
    (z₀ : Z) (hJ : C.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E))
    (hK : C.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0) (v : D) :
    C.mooreOperator J hα (z₀,v) =
      OAI.Analysis.Normed.Function.Holder.mooreDetField hα n
        ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) (C.background z₀) +
          ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp J.second) v) -
        C.source z₀ := by
  exact (C.mooreOperator_base J hα z₀ hJ hK v).trans
    (congrArg (fun H => OAI.Analysis.Normed.Function.Holder.mooreDetField hα n H - C.source z₀)
      ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).map_add _ _))

omit [Fintype ι] in
theorem ParameterJetFields.hasFDerivAt_base
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α)
    (z₀ : Z) (hJ : C.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E))
    (hK : C.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0) (v : D) :
    HasFDerivAt (fun w => C.mooreOperator J hα (z₀,w))
      ((fderiv ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα n)
        ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) (C.background z₀) +
          ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp J.second) v)).comp
        ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp J.second)) v := by
  exact (hasFDerivAt_mooreDetField_affine hα
    ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp J.second)
    ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) (C.background z₀))
    (C.source z₀) v).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun w => C.mooreOperator_base_affine J hα z₀ hJ hK w))

end OAI.Analysis.PDE.Schauder
