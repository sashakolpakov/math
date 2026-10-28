import OAI.Analysis.PDE.Schauder.Calculus.Parameter.MooreOperator

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
local instance parameterHessianDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance parameterHessianDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance parameterHessianSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterHessianSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterHessianEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance parameterHessianEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance parameterHessianMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance parameterHessianMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

def ParameterJetFields.hessianField (C : ParameterJetFields r α U e b)
    (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (p : Z × D) :
    OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)
    (C.background p.1 + transformedHessianField hα (C.jacobian p.1)
      (C.curvature p.1) (J.first p.2) (J.second p.2))

omit [Fintype ι] in
theorem ParameterJetFields.contDiffOn_hessianField
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) :
    ContDiffOn ℝ ∞ (C.hessianField J hα) {p | p.1 ∈ U} := by
  have hB₀ : ContDiffOn ℝ ∞ (fun p : Z × D => C.background p.1) {p | p.1 ∈ U} :=
    C.background_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hJ : ContDiffOn ℝ ∞ (fun p : Z × D => C.jacobian p.1) {p | p.1 ∈ U} :=
    C.jacobian_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hT : ContDiffOn ℝ ∞ (fun p : Z × D => C.curvature p.1) {p | p.1 ∈ U} :=
    C.curvature_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hp : ContDiffOn ℝ ∞ (fun p : Z × D => J.first p.2) {p | p.1 ∈ U} :=
    (J.first.contDiff.comp contDiff_snd).contDiffOn
  have hB : ContDiffOn ℝ ∞ (fun p : Z × D => J.second p.2) {p | p.1 ∈ U} :=
    (J.second.contDiff.comp contDiff_snd).contDiffOn
  let L : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α →L[ℝ]
      OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α :=
    OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)
  exact L.contDiff.comp_contDiffOn (hB₀.add (contDiffOn_transformedHessianField hα hJ hT hp hB))

omit [Fintype ι] in
theorem ParameterJetFields.hessianField_periodic
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b)
    (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α) {z : Z} (hz : z ∈ U) (v : D) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField J hα (z,v)))) := by
  apply holder_periodic_of_value_eq e b hr
  intro x y l hy
  have hBg := holder_value_eq_of_periodic e b (C.background z) (C.background_periodic z hz) x y l hy
  have hJ := holder_value_eq_of_periodic e b (C.jacobian z) (C.jacobian_periodic z hz) x y l hy
  have hT := holder_value_eq_of_periodic e b (C.curvature z) (C.curvature_periodic z hz) x y l hy
  have hp := holder_value_eq_of_periodic e b (J.first v) (J.first_periodic v) x y l hy
  have hB := holder_value_eq_of_periodic e b (J.second v) (J.second_periodic v) x y l hy
  change OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j =>
    (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background z) y +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedHessianField hα (C.jacobian z)
        (C.curvature z) (J.first v) (J.second v)) y) (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)) =
    OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j =>
    (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background z) x +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedHessianField hα (C.jacobian z)
        (C.curvature z) (J.first v) (J.second v)) x) (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j))
  congr 1
  funext i j
  simp only [add_apply,value_transformedHessianField,hBg,hJ,hT,hp,hB]

end OAI.Analysis.PDE.Schauder
