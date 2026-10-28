import OAI.Analysis.PDE.Schauder.Calculus.Parameter.JetFields
import OAI.Analysis.PDE.Schauder.Calculus.TransformedValue
import OAI.Analysis.PDE.Schauder.Calculus.LatticeJets
import OAI.Analysis.Normed.Operator.ClosedSubspace.CalculusClosedSubspace

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
local instance parameterOpDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance parameterOpDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance parameterOpSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterOpSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterOpEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance parameterOpEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance parameterOpMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance parameterOpMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

def ParameterJetFields.mooreOperator (C : ParameterJetFields r α U e b)
    (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (p : Z × D) :
    OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} ℝ α :=
  transformedBackgroundMooreField hα (C.background p.1) (C.jacobian p.1)
    (C.curvature p.1) (J.first p.2) (J.second p.2) - C.source p.1

omit [Fintype ι] in
theorem ParameterJetFields.contDiffOn_mooreOperator
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) :
    ContDiffOn ℝ ∞ (C.mooreOperator J hα) {p | p.1 ∈ U} := by
  have hB₀ : ContDiffOn ℝ ∞ (fun p : Z × D => C.background p.1) {p | p.1 ∈ U} :=
    C.background_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hJ : ContDiffOn ℝ ∞ (fun p : Z × D => C.jacobian p.1) {p | p.1 ∈ U} :=
    C.jacobian_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hT : ContDiffOn ℝ ∞ (fun p : Z × D => C.curvature p.1) {p | p.1 ∈ U} :=
    C.curvature_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hF : ContDiffOn ℝ ∞ (fun p : Z × D => C.source p.1) {p | p.1 ∈ U} :=
    C.source_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hp : ContDiffOn ℝ ∞ (fun p : Z × D => J.first p.2) {p | p.1 ∈ U} :=
    (J.first.contDiff.comp contDiff_snd).contDiffOn
  have hB : ContDiffOn ℝ ∞ (fun p : Z × D => J.second p.2) {p | p.1 ∈ U} :=
    (J.second.contDiff.comp contDiff_snd).contDiffOn
  exact (contDiffOn_transformedBackgroundMooreField hα hB₀ hJ hT hp hB).sub hF

theorem ParameterJetFields.mooreOperator_periodic
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b)
    (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α) {z : Z} (hz : z ∈ U) (v : D) :
    C.mooreOperator J hα (z,v) ∈ OAI.Analysis.Normed.Function.Holder.latticeHolder e b := by
  have hmain := transformedBackgroundMooreField_periodic e b hr hα
    (C.background z) (C.jacobian z) (C.curvature z) (J.first v) (J.second v)
    (C.background_periodic z hz) (C.jacobian_periodic z hz)
    (C.curvature_periodic z hz) (J.first_periodic v) (J.second_periodic v)
  exact (OAI.Analysis.Normed.Function.Holder.latticeHolder e b).sub_mem hmain (C.source_periodic z hz)

def ParameterJetFields.periodicOperator (C : ParameterJetFields r α U e b)
    (J : LatticeJetLifts hΩK α e b) (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α)
    (p : Z × D) : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e b := by
  classical
  exact if hz : p.1 ∈ U then
    ⟨C.mooreOperator J hα p,C.mooreOperator_periodic J hr hα hz p.2⟩ else 0

theorem ParameterJetFields.coe_periodicOperator (C : ParameterJetFields r α U e b)
    (J : LatticeJetLifts hΩK α e b) (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α)
    (p : Z × D) (hp : p.1 ∈ U) :
    (C.periodicOperator J hr hα p).val = C.mooreOperator J hα p := by
  simp only [ParameterJetFields.periodicOperator,dite_eq_left hp]

theorem ParameterJetFields.contDiffOn_periodicOperator (C : ParameterJetFields r α U e b)
    (J : LatticeJetLifts hΩK α e b) (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α)
    (hU : IsOpen U) : ContDiffOn ℝ ∞ (C.periodicOperator J hr hα) {p | p.1 ∈ U} := by
  apply OAI.Analysis.Normed.Operator.ClosedSubspace.contDiffOn_infty_of_isometry
    (OAI.Analysis.Normed.Function.Holder.latticeHolder (K := {x | r x ≤ 0}) (α := α) e b).subtypeₗᵢ (hU.preimage continuous_fst)
  exact (C.contDiffOn_mooreOperator J hα).congr
    (fun p hp => C.coe_periodicOperator J hr hα p hp)

end OAI.Analysis.PDE.Schauder
