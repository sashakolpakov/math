import OAI.Analysis.PDE.Schauder.Calculus.LatticeLinearization
import OAI.Analysis.PDE.Schauder.Calculus.Parameter.Zero
import OAI.Analysis.PDE.Schauder.Calculus.Parameter.SliceDerivative
import OAI.Analysis.PDE.Dirichlet.C2HolderPeriodicDerivative

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
local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
attribute [local instance] latticeJetsDualGroup latticeJetsDualSpace
  latticeJetsSecondGroup latticeJetsSecondSpace
local instance parameterInverseC2Group : NormedAddCommGroup H := inferInstance
local instance parameterInverseC2Space : NormedSpace ℝ H := inferInstance
local instance parameterInverseC2Module : Module ℝ H := inferInstance
local instance parameterInverseC2AddZero : AddZeroClass H := inferInstance
local instance parameterInverseC2Bounded : IsBoundedSMul ℝ H := NormedSpace.toIsBoundedSMul
local instance parameterInverseC2Continuous : ContinuousSMul ℝ H := IsBoundedSMul.continuousSMul

omit [Fintype ι] in
theorem ParameterJetFields.hasFDerivAt_base_slice
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α)
    (z₀ : Z) (hJ : C.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E))
    (hK : C.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0) (g : H) (v₀ : D)
    (hbase : C.background z₀ + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g) :
    HasFDerivAt (fun v : D => C.mooreOperator J hα (z₀,v))
      ((fderiv ℝ (OAI.Analysis.PDE.Dirichlet.mooreDirichletOperator hα OAI.Analysis.Calculus.Quaternion.fourSlots) g).comp
        (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL) v₀ := by
  exact (C.hasFDerivAt_base J hα z₀ hJ hK v₀).congr_fderiv
    (J.affine_linearization_eq hα (C.background z₀) g v₀ hbase)

theorem ParameterJetFields.coe_partial_fderiv_base
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b)
    (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α) (hU : IsOpen U)
    (z₀ : Z) (hz₀ : z₀ ∈ U)
    (hJ : C.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E))
    (hK : C.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0) (g : H) (v₀ w : D)
    (hbase : C.background z₀ + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g) :
    (((fderiv ℝ (C.periodicOperator J hr hα) (z₀,v₀)).comp
        (ContinuousLinearMap.inr ℝ Z D)) w).val =
      fderiv ℝ (OAI.Analysis.PDE.Dirichlet.mooreDirichletOperator hα OAI.Analysis.Calculus.Quaternion.fourSlots) g w.val := by
  have hQ : DifferentiableAt ℝ (C.periodicOperator J hr hα) (z₀,v₀) :=
    ((C.contDiffOn_periodicOperator J hr hα hU (z₀,v₀) hz₀).contDiffAt
      ((hU.preimage continuous_fst).mem_nhds hz₀)).differentiableAt (by simp)
  have he := coe_parameter_partial_fderiv_of_slice
    (OAI.Analysis.Normed.Function.Holder.latticeHolder (K := {x | r x ≤ 0}) (α := α) e b).subtypeL
    (C.periodicOperator J hr hα) (fun v : D => C.mooreOperator J hα (z₀,v))
    _ z₀ v₀ hQ (C.hasFDerivAt_base_slice J hα z₀ hJ hK g v₀ hbase)
    (fun v => C.coe_periodicOperator J hr hα (z₀,v) hz₀)
  exact congrArg (fun L => L w) he

theorem ParameterJetFields.partial_fderiv_base
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b)
    (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α) (hU : IsOpen U)
    (z₀ : Z) (hz₀ : z₀ ∈ U)
    (hJ : C.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E))
    (hK : C.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0)
    (hΩ : IsOpen {x | r x < 0}) (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    (hΩper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => r x < 0))
    (hKper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => r x ≤ 0))
    (g : H) (hg : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)))
    (v₀ : D) (hbase : C.background z₀ + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g) :
    (fderiv ℝ (C.periodicOperator J hr hα) (z₀,v₀)).comp
      (ContinuousLinearMap.inr ℝ Z D) =
        fderiv ℝ (OAI.Analysis.PDE.Dirichlet.periodicMooreDirichletOperator hΩ hclosure hΩper hKper hα OAI.Analysis.Calculus.Quaternion.fourSlots g hg) 0 := by
  ext w : 1
  apply Subtype.ext
  have hleft := C.coe_partial_fderiv_base J hr hα hU z₀ hz₀ hJ hK g v₀ w hbase
  have hright := OAI.Analysis.PDE.Dirichlet.fderiv_periodicMooreDirichletOperator_coe
    hΩ hclosure hΩper hKper hα OAI.Analysis.Calculus.Quaternion.fourSlots g hg (0 : D) w
  have heq : g + (0 : D).val = g := by simp only [ZeroMemClass.coe_zero,add_zero]
  exact hleft.trans ((congrArg
    (fun z : H => fderiv ℝ (OAI.Analysis.PDE.Dirichlet.mooreDirichletOperator hα OAI.Analysis.Calculus.Quaternion.fourSlots) z w.val) heq).symm.trans
      hright.symm)

theorem ParameterJetFields.partial_fderiv_base_isInvertible
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b)
    (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α) (hU : IsOpen U)
    (z₀ : Z) (hz₀ : z₀ ∈ U)
    (hJ : C.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E))
    (hK : C.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0)
    (hΩ : IsOpen {x | r x < 0}) (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    (hΩper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => r x < 0))
    (hKper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => r x ≤ 0))
    (g : H) (hg : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)))
    (v₀ : D) (hbase : C.background z₀ + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g)
    (hinv : (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.periodicMooreDirichletOperator hΩ hclosure hΩper hKper hα OAI.Analysis.Calculus.Quaternion.fourSlots g hg) 0).IsInvertible) :
    ((fderiv ℝ (C.periodicOperator J hr hα) (z₀,v₀)).comp
      (ContinuousLinearMap.inr ℝ Z D)).IsInvertible := by
  rw [C.partial_fderiv_base J hr hα hU z₀ hz₀ hJ hK hΩ hclosure hΩper hKper g hg v₀ hbase]
  exact hinv

end OAI.Analysis.PDE.Schauder
