import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Zero
import OAI.Analysis.PDE.Schauder.Calculus.Periodic.DeformationOperator
import OAI.Analysis.PDE.Schauder.Calculus.SliceDerivative
import OAI.Analysis.PDE.Schauder.Calculus.LinearizationAlgebra

open Set Module
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {I : Set ℝ}
  {Φ : ℝ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
  {B₀ f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
local notation "A" => OAI.Analysis.Normed.Function.Holder.HolderMap (Set.ofPred (fun x : E => r x ≤ 0)) (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α
attribute [local instance] latticeJetsDualGroup latticeJetsDualSpace
  latticeJetsSecondGroup latticeJetsSecondSpace
local instance diffEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance diffEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance diffMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance diffMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance diffC2Group : NormedAddCommGroup H := inferInstance
local instance diffC2Space : NormedSpace ℝ H := inferInstance
local instance diffC2Module : Module ℝ H := inferInstance
local instance diffC2Bounded : IsBoundedSMul ℝ H := NormedSpace.toIsBoundedSMul
local instance diffC2Continuous : ContinuousSMul ℝ H := IsBoundedSMul.continuousSMul
local instance diffC2AddZero : AddZeroClass H := inferInstance

theorem mooreDirichlet_fderiv_factorization (hα : 0 ≤ α) (g : H) :
    fderiv ℝ (OAI.Analysis.PDE.Dirichlet.mooreDirichletOperator hα OAI.Analysis.Calculus.Quaternion.fourSlots) g =
      (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα n) (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots g)).comp
        (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots) := by
  exact (hasFDerivAt_mooreDetField_comp hα (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots) g).fderiv

omit [Fintype ι] in
theorem LatticeJetLifts.hessian_map_eq (J : LatticeJetLifts hΩK α e b) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM.comp
      (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL = J.second := by
  ext v : 1
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective (J.second_value v)).symm

omit [Fintype ι] in
theorem LatticeJetLifts.quaternion_map_eq (J : LatticeJetLifts hΩK α e b) :
    (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots).comp
        (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL =
      (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp J.second := by
  have hh := congrArg
    (fun L => (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp L)
    J.hessian_map_eq
  simpa only [OAI.Analysis.PDE.Dirichlet.quaternionHessianField,ContinuousLinearMap.comp_assoc] using! hh

omit [Fintype ι] in
theorem DeformationFields.quaternion_base_relation
    (C : DeformationFields r α I Φ B₀ f) (J : LatticeJetLifts hΩK α e b)
    (g : H) (v₀ : X)
    (hbase : C.background 0 + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g) :
    (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) (C.background 0) +
      ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp J.second) v₀ =
        OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots g := by
  have hb := congrArg (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) hbase
  simpa only [map_add] using! hb

omit [Fintype ι] in
theorem DeformationFields.mooreOperator_zero_affine
    (C : DeformationFields r α I Φ B₀ f) (J : LatticeJetLifts hΩK α e b)
    (hI : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x) (hα : 0 ≤ α) :
    (fun v : X => C.mooreOperator hα J.first J.second (0,v)) =
      (fun v : X => OAI.Analysis.Normed.Function.Holder.mooreDetField hα n
        ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) (C.background 0) +
          ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp J.second) v) - C.source 0) := by
  funext v
  exact C.mooreOperator_zero_affine_general hI hΦ hα J.first J.second v

omit [Fintype ι] in
theorem DeformationFields.zero_slice_linearization_eq
    (C : DeformationFields r α I Φ B₀ f) (J : LatticeJetLifts hΩK α e b)
    (hα : 0 ≤ α) (g : H) (v₀ : X)
    (hbase : C.background 0 + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g) :
    (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα n)
      ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) (C.background 0) +
        ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp J.second) v₀)).comp
      ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp J.second) =
      ((fderiv ℝ (OAI.Analysis.PDE.Dirichlet.mooreDirichletOperator hα OAI.Analysis.Calculus.Quaternion.fourSlots) g).comp
        (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL) := by
  let pin := (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL
  have hb := congrArg (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα n))
    (C.quaternion_base_relation J g v₀ hbase)
  have hm := congrArg (fun T => T.comp pin)
    (mooreDirichlet_fderiv_factorization hα g)
  have hh := congrArg₂ (fun F L => F.comp L) hb J.quaternion_map_eq.symm
  exact hh.trans ((ContinuousLinearMap.comp_assoc _ _ _).symm.trans hm.symm)

omit [Fintype ι] in
theorem DeformationFields.hasFDerivAt_zero_slice
    (C : DeformationFields r α I Φ B₀ f) (J : LatticeJetLifts hΩK α e b)
    (hI : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x) (hα : 0 ≤ α)
    (g : H) (v₀ : X)
    (hbase : C.background 0 + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g) :
    HasFDerivAt (fun v : X => C.mooreOperator hα J.first J.second (0,v))
      ((fderiv ℝ (OAI.Analysis.PDE.Dirichlet.mooreDirichletOperator hα OAI.Analysis.Calculus.Quaternion.fourSlots) g).comp
        (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL) v₀ := by
  exact (C.hasFDerivAt_zero_general hI hΦ hα J.first J.second v₀).congr_fderiv
    (C.zero_slice_linearization_eq J hα g v₀ hbase)

theorem PeriodicDeformationFields.coe_partial_fderiv_zero
    (C : PeriodicDeformationFields r α I Φ B₀ f e b) (J : LatticeJetLifts hΩK α e b)
    (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α) (hI : IsOpen I) (h0 : 0 ∈ I)
    (hΦ : ∀ x, Φ (0,x) = x) (g : H) (v₀ w : X)
    (hbase : C.fields.background 0 + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g) :
    (((fderiv ℝ (C.periodicOperator J hr hα) (0,v₀)).comp
        (ContinuousLinearMap.inr ℝ ℝ X)) w).val =
      fderiv ℝ (OAI.Analysis.PDE.Dirichlet.mooreDirichletOperator hα OAI.Analysis.Calculus.Quaternion.fourSlots) g w.val := by
  have hQ : DifferentiableAt ℝ (C.periodicOperator J hr hα) (0,v₀) :=
    ((C.contDiffOn_periodicOperator J hr hα hI (0,v₀) h0).contDiffAt
      ((hI.preimage continuous_fst).mem_nhds h0)).differentiableAt (by simp)
  have he := coe_partial_fderiv_of_slice
    (OAI.Analysis.Normed.Function.Holder.latticeHolder (K := {x | r x ≤ 0}) (α := α) e b).subtypeL
    (C.periodicOperator J hr hα)
    (fun v : X => C.fields.mooreOperator hα J.first J.second (0,v))
    _ v₀ hQ (C.fields.hasFDerivAt_zero_slice J h0 hΦ hα g v₀ hbase)
    (fun v => C.coe_periodicOperator J hr hα (0,v) h0)
  exact congrArg (fun L => L w) he

end OAI.Analysis.PDE.Schauder
