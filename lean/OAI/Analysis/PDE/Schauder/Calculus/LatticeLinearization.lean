import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Differential
import OAI.Analysis.PDE.Schauder.Calculus.ImplicitLinearizationAlgebra

open Set Module
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
attribute [local instance] latticeJetsDualGroup latticeJetsDualSpace
  latticeJetsSecondGroup latticeJetsSecondSpace
local instance latticeLinearC2Group : NormedAddCommGroup H := inferInstance
local instance latticeLinearC2Space : NormedSpace ℝ H := inferInstance
local instance latticeLinearC2Module : Module ℝ H := inferInstance
local instance latticeLinearC2Bounded : IsBoundedSMul ℝ H := NormedSpace.toIsBoundedSMul
local instance latticeLinearC2Continuous : ContinuousSMul ℝ H := IsBoundedSMul.continuousSMul
local instance latticeLinearC2AddZero : AddZeroClass H := inferInstance

omit [Fintype ι] in
theorem LatticeJetLifts.quaternion_base_relation
    (J : LatticeJetLifts hΩK α e b)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α)
    (g : H) (v₀ : X) (hbase : B + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g) :
    (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) B +
      ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp J.second) v₀ =
        OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots g := by
  have hb := congrArg (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) hbase
  simpa only [map_add] using! hb

omit [Fintype ι] in
theorem LatticeJetLifts.affine_linearization_eq
    (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α)
    (g : H) (v₀ : X) (hbase : B + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g) :
    (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα n)
      ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) B +
        ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp J.second) v₀)).comp
      ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp J.second) =
      ((fderiv ℝ (OAI.Analysis.PDE.Dirichlet.mooreDirichletOperator hα OAI.Analysis.Calculus.Quaternion.fourSlots) g).comp
        (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL) := by
  let pin := (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL
  have hb := congrArg (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα n))
    (J.quaternion_base_relation B g v₀ hbase)
  have hm := congrArg (fun T => T.comp pin)
    (mooreDirichlet_fderiv_factorization hα g)
  have hh := congrArg₂ (fun F L => F.comp L) hb J.quaternion_map_eq.symm
  exact hh.trans ((ContinuousLinearMap.comp_assoc _ _ _).symm.trans hm.symm)

end OAI.Analysis.PDE.Schauder
