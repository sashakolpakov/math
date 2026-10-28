import OAI.Analysis.Fourier.WavePackets.Dirichlet.Closed
import OAI.Analysis.Fourier.WavePackets.ParameterBaseAlgebra
import OAI.Analysis.Normed.Function.Holder.C2HolderEquationLimit
import OAI.Analysis.PDE.Dirichlet.Boundary.Tangential

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b}
  {α : ℝ} {U : Set Z}
  {hΩK : {x | D.defining x < 0} ⊆ {x | D.defining x ≤ 0}}

local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4
local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
attribute [local instance] OAI.Analysis.PDE.Schauder.latticeJetsDualGroup OAI.Analysis.PDE.Schauder.latticeJetsDualSpace
  OAI.Analysis.PDE.Schauder.latticeJetsSecondGroup OAI.Analysis.PDE.Schauder.latticeJetsSecondSpace
local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance : NormedAddCommGroup H := inferInstance
local instance : NormedSpace ℝ H := inferInstance
local instance : Module ℝ H := inferInstance
local instance : IsBoundedSMul ℝ H := NormedSpace.toIsBoundedSMul
local instance : ContinuousSMul ℝ H := IsBoundedSMul.continuousSMul
local instance : AddZeroClass H := inferInstance

omit [CompleteSpace Z] in
/-- A genuine classical solution supplies the actual Banach base point,
zero residual and strict positivity required by the parameter IFT. -/
theorem PeriodicQuaternionicSolution.parameter_base_of_jets
    (S : PeriodicQuaternionicSolution D)
    (C : OAI.Analysis.PDE.Schauder.ParameterJetFields D.defining α U e b)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (_ : α ≤ 1)
    {z₀ : Z} (hz₀ : z₀ ∈ U)
    (hJ : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian z₀) x = ContinuousLinearMap.id ℝ E)
    (hK : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature z₀) x = 0)
    (hB : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background z₀) x =
      fderiv ℝ (fderiv ℝ D.background) x)
    (hF : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source z₀) x = D.density x)
    (v₀ : X) (g : H)
    (hv₂ : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative v₀.val x =
      fderiv ℝ (fderiv ℝ S.u) x)
    (hg₂ : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x =
      fderiv ℝ (fderiv ℝ (fun y => D.background y + S.u y)) x) :
      C.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E) ∧
      C.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0 ∧
      C.background z₀ + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g ∧
      C.periodicOperator J D.defining_periodic hα (z₀,v₀) = 0 ∧
      C.PositiveAt J hα (z₀,v₀) := by
  have hj : C.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E) := by
    apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
    exact BoundedContinuousFunction.ext hJ
  have hk : C.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0 := by
    apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
    exact BoundedContinuousFunction.ext hK
  have hsum (x : {x | D.defining x ≤ 0}) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background z₀) x + OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative v₀.val x =
        OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x := by
    rw [hB,hv₂,hg₂]
    exact (OAI.Analysis.PDE.Dirichlet.second_fderiv_add (D.background_smooth.of_le (by simp))
      (S.smooth.of_le (by simp)) x).symm
  have hbase := holder_add_second_eq J v₀ g (C.background z₀) hsum
  have hq (x : {x | D.defining x ≤ 0}) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots g) x =
        OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => D.background y + S.u y) x :=
    OAI.Analysis.PDE.Dirichlet.quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots g _ x (hg₂ x)
  have hh := parameter_hessianField_base C J hα z₀ v₀ g hj hk hbase
  refine ⟨hj,hk,hbase,?_,?_⟩
  · apply parameter_periodicOperator_zero C J D.defining_periodic hα hz₀ v₀
    intro x
    rw [hh,hq,hF,S.closed_equation x x.property]
  · unfold OAI.Analysis.PDE.Schauder.ParameterJetFields.PositiveAt
    rw [hh]
    intro x q hq'
    rw [hq]
    exact (OAI.Analysis.PDE.Dirichlet.complexify_posDef_iff_unit_sphere _
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots ((D.background_smooth.add S.smooth).of_le (by simp)).contDiffAt)).mp
      (S.closed_positive x x.property) q hq'

structure ClassicalParameterBase
    (S : PeriodicQuaternionicSolution D) (C : OAI.Analysis.PDE.Schauder.ParameterJetFields D.defining α U e b)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (z₀ : Z) where
  correction : X
  full : H
  value : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value correction.val x = S.u x
  second : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative full x =
    fderiv ℝ (fderiv ℝ (fun y => D.background y + S.u y)) x
  periodic : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value full))
  jacobian : C.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E)
  curvature : C.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0
  hessian : C.background z₀ + J.second correction = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM full
  zero : C.periodicOperator J D.defining_periodic hα (z₀,correction) = 0
  positive : C.PositiveAt J hα (z₀,correction)

omit [CompleteSpace Z] in
theorem PeriodicQuaternionicSolution.nonempty_parameter_base
    (S : PeriodicQuaternionicSolution D) (C : OAI.Analysis.PDE.Schauder.ParameterJetFields D.defining α U e b)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {z₀ : Z} (hz₀ : z₀ ∈ U)
    (hJ : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian z₀) x = ContinuousLinearMap.id ℝ E)
    (hK : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature z₀) x = 0)
    (hB : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background z₀) x =
      fderiv ℝ (fderiv ℝ D.background) x)
    (hF : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source z₀) x = D.density x) :
    Nonempty (ClassicalParameterBase S C J hα z₀) := by
  obtain ⟨v₀,g,hv₀,hv₁,hv₂,hg₂,hg₀,hgp⟩ := S.exists_full_banach_jet (hΩD := hΩK) hα hα1
  have hb := S.parameter_base_of_jets C J hα hα1 hz₀ hJ hK hB hF v₀ g hv₂ hg₂
  exact ⟨⟨v₀,g,hv₀,hg₂,hgp,hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2⟩⟩

end OAI.Analysis.Fourier.WavePackets
