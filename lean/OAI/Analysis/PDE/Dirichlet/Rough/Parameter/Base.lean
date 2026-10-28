import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.SolutionCurves
import OAI.Analysis.PDE.Schauder.Calculus.Parameter.Zero

noncomputable section
open Set Module
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : CoordinateSpace n 4 → ℝ} {α : ℝ} {U : Set Z}
  {Φ : Z × CoordinateSpace n 4 → CoordinateSpace n 4}
  {B₀ : CoordinateSpace n 4 → ℝ}
  {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => CoordinateSpace n 4
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α

local instance parameterBaseDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance parameterBaseDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance parameterBaseSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterBaseSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterBaseEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance parameterBaseEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance parameterBaseMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance parameterBaseMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance parameterBaseC2Group : NormedAddCommGroup H := inferInstance
local instance parameterBaseC2Space : NormedSpace ℝ H := inferInstance
local instance parameterBaseC2Module : Module ℝ H := inferInstance
local instance parameterBaseC2Bounded : IsBoundedSMul ℝ H := NormedSpace.toIsBoundedSMul
local instance parameterBaseC2Continuous : ContinuousSMul ℝ H := IsBoundedSMul.continuousSMul
local instance parameterBaseC2AddZero : AddZeroClass H := inferInstance

omit [Fintype ι] in
theorem parameter_jacobian_zero
    (C : OAI.Analysis.PDE.Schauder.ParameterJetFields r α U e b) (hΦ : ∀ x, Φ (0,x) = x)
    (hJ : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian 0) x = ParameterDeformation.inverseJacobian Φ (0,x)) :
    C.jacobian 0 = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E) := by
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
  apply BoundedContinuousFunction.ext
  intro x
  rw [hJ,OAI.Analysis.Normed.Function.Holder.HolderMap.value_constant,ParameterDeformation.inverseJacobian_zero hΦ]

omit [Fintype ι] in
theorem parameter_curvature_zero
    (C : OAI.Analysis.PDE.Schauder.ParameterJetFields r α U e b) (hΦ : ∀ x, Φ (0,x) = x)
    (hT : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature 0) x = ParameterDeformation.inverseHessian Φ (0,x)) :
    C.curvature 0 = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0 := by
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
  apply BoundedContinuousFunction.ext
  intro x
  rw [hT,OAI.Analysis.Normed.Function.Holder.HolderMap.value_constant,ParameterDeformation.inverseHessian_zero hΦ]

omit [Fintype ι] in
theorem parameter_background_add_second_eq
    (C : OAI.Analysis.PDE.Schauder.ParameterJetFields r α U e b) (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b)
    (hΦ : ∀ x, Φ (0,x) = x) (B : H)
    (hB : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative B x = fderiv ℝ (fderiv ℝ B₀) x)
    (hBg : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background 0) x = fderiv ℝ (fderiv ℝ B₀) (Φ (0,x)))
    (v : X) : C.background 0 + J.second v = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM (B+v.val) := by
  have hb : C.background 0 = B.val.2.2 := by
    apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
    apply BoundedContinuousFunction.ext
    intro x
    rw [hBg,hΦ]
    exact (hB x).symm
  have hv : J.second v = v.val.val.2.2 :=
    OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective (J.second_value v)
  change C.background 0 + J.second v = B.val.2.2 + v.val.val.2.2
  exact congrArg₂ (· + ·) hb hv

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
