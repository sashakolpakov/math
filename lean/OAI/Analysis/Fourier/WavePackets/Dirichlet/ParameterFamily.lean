import OAI.Analysis.Fourier.WavePackets.Dirichlet.ParameterBase
import OAI.Analysis.PDE.Schauder.Calculus.Parameter.Inverse
import OAI.Analysis.PDE.Dirichlet.UnconditionalLinear
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Inverse
import OAI.Analysis.PDE.Schauder.Calculus.PositiveImplicitFamilyOpen

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Module Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise Topology

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
  [Fintype ι]
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

omit [CompleteSpace Z] [FiniteDimensional ℝ P] in
/-- The parameter derivative at a genuine solution is invertible. The
linear Dirichlet inverse and the actual full-potential jet are used, rather
than assuming invertibility of the transformed residual. -/
theorem PeriodicQuaternionicSolution.parameter_partial_isInvertible
    [Nonempty {x | D.defining x ≤ 0}]
    (S : PeriodicQuaternionicSolution D)
    (C : OAI.Analysis.PDE.Schauder.ParameterJetFields D.defining α U e b)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 < α) (hα1 : α < 1)
    (hU : IsOpen U) {z₀ : Z} (hz₀ : z₀ ∈ U)
    (hj : C.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E))
    (hk : C.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0)
    (v₀ : X) (g : H)
    (hg : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)))
    (hg₂ : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x =
      fderiv ℝ (fderiv ℝ (fun y => D.background y + S.u y)) x)
    (hbase : C.background z₀ + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g) :
    ((fderiv ℝ (C.periodicOperator J D.defining_periodic hα.le) (z₀,v₀)).comp
      (ContinuousLinearMap.inr ℝ Z X)).IsInvertible := by
  apply C.partial_fderiv_base_isInvertible J D.defining_periodic hα.le hU z₀ hz₀ hj hk
    (isOpen_lt D.defining_smooth.continuous continuous_const) D.closed_subset_closure
    (D.defining_periodic.comp (fun t => t < 0))
    (D.defining_periodic.comp (fun t => t ≤ 0)) g hg v₀ hbase
  exact S.full_jet_inverse hα hα1 g hg hg₂

omit [FiniteDimensional ℝ P] in
theorem ClassicalParameterBase.exists_positive_family
    [Nonempty {x | D.defining x ≤ 0}]
    {S : PeriodicQuaternionicSolution D} {C : OAI.Analysis.PDE.Schauder.ParameterJetFields D.defining α U e b}
    {J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b} (hα : 0 < α) (hα1 : α < 1)
    (hU : IsOpen U) {z₀ : Z} (hz₀ : z₀ ∈ U)
    (B : ClassicalParameterBase S C J hα.le z₀) :
    ∃ (v : Z → X) (W : Set Z), IsOpen W ∧ z₀ ∈ W ∧ W ⊆ U ∧
      ContDiffOn ℝ ∞ v W ∧
      (∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value (v z₀).val x = S.u x) ∧
      ∀ z ∈ W, C.periodicOperator J D.defining_periodic hα.le (z,v z) = 0 ∧
        C.PositiveAt J hα.le (z,v z) := by
  have hder := S.parameter_partial_isInvertible C J hα hα1 hU hz₀ B.jacobian B.curvature
    B.correction B.full B.periodic B.second B.hessian
  obtain ⟨v,W,hW,hW0,hWU,hv,hv0,hev⟩ := C.exists_positive_implicit_family_open J D.compact
    D.defining_smooth.continuous D.defining_periodic D.bounded hα.le hU hz₀ B.correction B.zero hder B.positive
  refine ⟨v,W,hW,hW0,hWU,hv,?_,hev⟩
  simpa only [hv0] using B.value

omit [FiniteDimensional ℝ P] in
/-- Actual classical solutions and exact base coefficient identities give
a smooth positive parameter branch. All Banach jets and the inverse are
constructed internally. -/
theorem PeriodicQuaternionicSolution.exists_positive_parameter_family
    [Nonempty {x | D.defining x ≤ 0}]
    (S : PeriodicQuaternionicSolution D)
    (C : OAI.Analysis.PDE.Schauder.ParameterJetFields D.defining α U e b)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 < α) (hα1 : α < 1)
    (hU : IsOpen U) {z₀ : Z} (hz₀ : z₀ ∈ U)
    (hJ : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian z₀) x = ContinuousLinearMap.id ℝ E)
    (hK : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature z₀) x = 0)
    (hB : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background z₀) x =
      fderiv ℝ (fderiv ℝ D.background) x)
    (hF : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source z₀) x = D.density x) :
    ∃ (v : Z → X) (W : Set Z), IsOpen W ∧ z₀ ∈ W ∧ W ⊆ U ∧
      ContDiffOn ℝ ∞ v W ∧
      (∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value (v z₀).val x = S.u x) ∧
      ∀ z ∈ W, C.periodicOperator J D.defining_periodic hα.le (z,v z) = 0 ∧
        C.PositiveAt J hα.le (z,v z) := by
  obtain ⟨B⟩ := S.nonempty_parameter_base C J hα.le hα1.le hz₀ hJ hK hB hF
  exact B.exists_positive_family hα hα1 hU hz₀

end OAI.Analysis.Fourier.WavePackets
