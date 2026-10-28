import OAI.Analysis.PDE.Schauder.Calculus.Parameter.Hessian
import OAI.Analysis.PDE.Schauder.Calculus.ImplicitFamily
import OAI.Analysis.PDE.Schauder.Calculus.HolderPositivity

open Set Metric Filter Module
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {U : Set Z}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "D" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
local instance familyPositiveDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance familyPositiveDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance familyPositiveSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance familyPositiveSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def ParameterJetFields.PositiveAt (C : ParameterJetFields r α U e b)
    (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (p : Z × D) : Prop :=
  ∀ x : {x | r x ≤ 0}, ∀ q ∈ sphere (0 : Fin n → Quaternion ℝ) 1,
    0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField J hα p) x) q).re

omit [CompleteSpace Z] in
theorem ParameterJetFields.eventually_positive_hessianField
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b)
    {K : Set V} (hK : IsCompact K) (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hα : 0 ≤ α) (hU : IsOpen U) {z₀ : Z} (hz₀ : z₀ ∈ U) (v₀ : D)
    (hpos : C.PositiveAt J hα (z₀,v₀)) :
    ∀ᶠ p : Z × D in 𝓝 (z₀,v₀), p.1 ∈ U ∧ C.PositiveAt J hα p := by
  have hopen : IsOpen {p : Z × D | p.1 ∈ U} := hU.preimage continuous_fst
  have hA : ContinuousAt (C.hessianField J hα) (z₀,v₀) :=
    ((C.contDiffOn_hessianField J hα (z₀,v₀) hz₀).contDiffAt
      (hopen.mem_nhds hz₀)).continuousAt
  have hnear : ∀ᶠ p : Z × D in 𝓝 (z₀,v₀), p.1 ∈ U := hopen.mem_nhds hz₀
  have hp := eventually_unit_positive_periodic_holder e b hK hr hrp hbounded
    (C.hessianField J hα) hA
    (hnear.mono (fun p hp => C.hessianField_periodic J hrp hα hp p.2)) hpos
  exact hnear.and hp

theorem ParameterJetFields.exists_implicit_family_near
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b)
    (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hα : 0 ≤ α) (hU : IsOpen U) {z₀ : Z} (hz₀ : z₀ ∈ U) (v₀ : D)
    (hzero : C.periodicOperator J hrp hα (z₀,v₀) = 0)
    (hder : ((fderiv ℝ (C.periodicOperator J hrp hα) (z₀,v₀)).comp
      (ContinuousLinearMap.inr ℝ Z D)).IsInvertible)
    {N : Set (Z × D)} (hN : N ∈ 𝓝 (z₀,v₀)) :
    ∃ v : Z → D, ContDiffAt ℝ ∞ v z₀ ∧ v z₀ = v₀ ∧
      ∀ᶠ z in 𝓝 z₀, (z,v z) ∈ N ∧ C.periodicOperator J hrp hα (z,v z) = 0 := by
  let : Fact (IsOpen {x | r x < 0}) := ⟨isOpen_lt hr continuous_const⟩
  have hopen : IsOpen {p : Z × D | p.1 ∈ U} := hU.preimage continuous_fst
  have hQ := (C.contDiffOn_periodicOperator J hrp hα hU (z₀,v₀) hz₀).contDiffAt
    (hopen.mem_nhds hz₀)
  exact exists_smooth_implicit_family (C.periodicOperator J hrp hα) z₀ v₀ hQ hzero hder hN

theorem ParameterJetFields.exists_positive_implicit_family
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b)
    {K : Set V} (hK : IsCompact K) (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hα : 0 ≤ α) (hU : IsOpen U) {z₀ : Z} (hz₀ : z₀ ∈ U) (v₀ : D)
    (hzero : C.periodicOperator J hrp hα (z₀,v₀) = 0)
    (hder : ((fderiv ℝ (C.periodicOperator J hrp hα) (z₀,v₀)).comp
      (ContinuousLinearMap.inr ℝ Z D)).IsInvertible)
    (hpos : C.PositiveAt J hα (z₀,v₀)) :
    ∃ v : Z → D, ContDiffAt ℝ ∞ v z₀ ∧ v z₀ = v₀ ∧
      ∀ᶠ z in 𝓝 z₀, z ∈ U ∧ C.periodicOperator J hrp hα (z,v z) = 0 ∧
        C.PositiveAt J hα (z,v z) := by
  let N : Set (Z × D) := {p | p.1 ∈ U ∧ C.PositiveAt J hα p}
  have hN : N ∈ 𝓝 (z₀,v₀) := C.eventually_positive_hessianField J hK hr hrp hbounded hα hU hz₀ v₀ hpos
  obtain ⟨v,hv,hv0,hev⟩ := C.exists_implicit_family_near J hr hrp hα hU hz₀ v₀ hzero hder hN
  refine ⟨v,hv,hv0,?_⟩
  filter_upwards [hev] with z hz
  exact ⟨hz.1.1,hz.2,hz.1.2⟩

end OAI.Analysis.PDE.Schauder
