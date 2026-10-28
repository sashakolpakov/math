import OAI.Analysis.PDE.Schauder.Calculus.PositiveImplicitFamily
import OAI.Analysis.PDE.Schauder.Calculus.Parameter.Zero

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped ContDiff Matrix.Norms.Elementwise

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 → ℝ} {α : ℝ} {U : Set Z}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4
local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
attribute [local instance] OAI.Analysis.PDE.Schauder.latticeJetsDualGroup OAI.Analysis.PDE.Schauder.latticeJetsDualSpace
  OAI.Analysis.PDE.Schauder.latticeJetsSecondGroup OAI.Analysis.PDE.Schauder.latticeJetsSecondSpace
local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

omit [Fintype ι] in
theorem holder_add_second_eq (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (v : X) (g : H)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α)
    (h : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x + OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative v.val x =
      OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x) : B + J.second v = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g := by
  have hv : J.second v = v.val.val.2.2 := OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective (J.second_value v)
  change B + J.second v = g.val.2.2
  rw [hv]
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
  exact BoundedContinuousFunction.ext h

omit [CompleteSpace Z] [Fintype ι] in
theorem parameter_hessianField_base (C : OAI.Analysis.PDE.Schauder.ParameterJetFields r α U e b)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (z₀ : Z) (v₀ : X) (g : H)
    (hj : C.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E))
    (hk : C.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0)
    (hbase : C.background z₀ + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g) :
    C.hessianField J hα (z₀,v₀) = OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots g := by
  exact (C.hessianField_base J hα z₀ hj hk v₀).trans
    (congrArg (OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) hbase)

omit [CompleteSpace Z] [Fintype ι] in
theorem parameter_mooreOperator_eq_hessianField (C : OAI.Analysis.PDE.Schauder.ParameterJetFields r α U e b)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (z : Z) (v : X) :
    C.mooreOperator J hα (z,v) = OAI.Analysis.Normed.Function.Holder.mooreDetField hα m (C.hessianField J hα (z,v)) - C.source z := rfl

omit [CompleteSpace Z] in
theorem parameter_periodicOperator_zero (C : OAI.Analysis.PDE.Schauder.ParameterJetFields r α U e b)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α)
    {z₀ : Z} (hz₀ : z₀ ∈ U) (v₀ : X)
    (heq : ∀ x : {x | r x ≤ 0}, OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField J hα (z₀,v₀)) x) =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source z₀) x) :
    C.periodicOperator J hr hα (z₀,v₀) = 0 := by
  apply Subtype.ext
  rw [C.coe_periodicOperator J hr hα (z₀,v₀) hz₀,parameter_mooreOperator_eq_hessianField]
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
  apply BoundedContinuousFunction.ext
  intro x
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.Normed.Function.Holder.mooreDetField hα m (C.hessianField J hα (z₀,v₀))) x -
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source z₀) x = 0
  rw [OAI.Analysis.Normed.Function.Holder.value_mooreDetField,heq x,sub_self]

end OAI.Analysis.Fourier.WavePackets
