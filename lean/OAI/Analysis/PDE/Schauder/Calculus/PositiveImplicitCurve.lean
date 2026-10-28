import OAI.Analysis.PDE.Schauder.Calculus.ImplicitCurve
import OAI.Analysis.PDE.Schauder.Calculus.Deformation.HessianPeriodic
import OAI.Analysis.PDE.Schauder.Calculus.HolderPositivity
import OAI.Analysis.PDE.Schauder.Calculus.Periodic.DeformationOperator

open Set Metric Filter Module
open scoped Topology ContDiff Matrix.Norms.Elementwise
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
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance positiveDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance positiveDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance positiveSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance positiveSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def DeformationFields.PositiveAt (C : DeformationFields r α I Φ B₀ f)
    (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (p : ℝ × X) : Prop :=
  ∀ x : {x | r x ≤ 0}, ∀ z ∈ sphere (0 : Fin n → Quaternion ℝ) 1,
    0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField hα J.first J.second p) x) z).re

theorem PeriodicDeformationFields.eventually_positive_hessianField
    (C : PeriodicDeformationFields r α I Φ B₀ f e b) (J : LatticeJetLifts hΩK α e b)
    {K : Set V} (hK : IsCompact K) (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hα : 0 ≤ α) (hI : IsOpen I) (h0 : 0 ∈ I) (v₀ : X)
    (hpos : C.fields.PositiveAt J hα (0,v₀)) :
    ∀ᶠ p : ℝ × X in 𝓝 (0,v₀), p.1 ∈ I ∧ C.fields.PositiveAt J hα p := by
  have hopen : IsOpen {p : ℝ × X | p.1 ∈ I} := hI.preimage continuous_fst
  have hA : ContinuousAt (C.fields.hessianField hα J.first J.second) (0,v₀) :=
    ((C.fields.contDiffOn_hessianField hα J.first J.second (0,v₀) h0).contDiffAt
      (hopen.mem_nhds h0)).continuousAt
  have hnear : ∀ᶠ p : ℝ × X in 𝓝 (0,v₀), p.1 ∈ I := hopen.mem_nhds h0
  have hp := eventually_unit_positive_periodic_holder e b hK hr hrp hbounded
    (C.fields.hessianField hα J.first J.second) hA
    (hnear.mono (fun p hp => C.hessianField_periodic J hrp hα hp p.2)) hpos
  exact hnear.and hp

theorem PeriodicDeformationFields.exists_implicit_curve_near
    (C : PeriodicDeformationFields r α I Φ B₀ f e b) (J : LatticeJetLifts hΩK α e b)
    (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hα : 0 ≤ α) (hI : IsOpen I) (h0 : 0 ∈ I) (v₀ : X)
    (hzero : C.periodicOperator J hrp hα (0,v₀) = 0)
    (hder : ((fderiv ℝ (C.periodicOperator J hrp hα) (0,v₀)).comp
      (ContinuousLinearMap.inr ℝ ℝ X)).IsInvertible)
    {N : Set (ℝ × X)} (hN : N ∈ 𝓝 (0,v₀)) :
    ∃ v : ℝ → X, ContDiffAt ℝ ∞ v 0 ∧ v 0 = v₀ ∧
      ∀ᶠ t in 𝓝 0, (t,v t) ∈ N ∧ C.periodicOperator J hrp hα (t,v t) = 0 := by
  let : Fact (IsOpen {x | r x < 0}) := ⟨isOpen_lt hr continuous_const⟩
  have hopen : IsOpen {p : ℝ × X | p.1 ∈ I} := hI.preimage continuous_fst
  have hQ := (C.contDiffOn_periodicOperator J hrp hα hI (0,v₀) h0).contDiffAt
    (hopen.mem_nhds h0)
  exact exists_smooth_implicit_curve (C.periodicOperator J hrp hα) v₀ hQ hzero hder hN

theorem PeriodicDeformationFields.exists_positive_implicit_curve
    (C : PeriodicDeformationFields r α I Φ B₀ f e b) (J : LatticeJetLifts hΩK α e b)
    {K : Set V} (hK : IsCompact K) (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hα : 0 ≤ α) (hI : IsOpen I) (h0 : 0 ∈ I) (v₀ : X)
    (hzero : C.periodicOperator J hrp hα (0,v₀) = 0)
    (hder : ((fderiv ℝ (C.periodicOperator J hrp hα) (0,v₀)).comp
      (ContinuousLinearMap.inr ℝ ℝ X)).IsInvertible)
    (hpos : C.fields.PositiveAt J hα (0,v₀)) :
    ∃ v : ℝ → X, ContDiffAt ℝ ∞ v 0 ∧ v 0 = v₀ ∧
      ∀ᶠ t in 𝓝 0, t ∈ I ∧ C.periodicOperator J hrp hα (t,v t) = 0 ∧
        C.fields.PositiveAt J hα (t,v t) := by
  let N : Set (ℝ × X) := {p | p.1 ∈ I ∧ C.fields.PositiveAt J hα p}
  have hN : N ∈ 𝓝 (0,v₀) := C.eventually_positive_hessianField J hK hr hrp hbounded hα hI h0 v₀ hpos
  obtain ⟨v,hv,hv0,hev⟩ := C.exists_implicit_curve_near J hr hrp hα hI h0 v₀ hzero hder hN
  refine ⟨v,hv,hv0,?_⟩
  filter_upwards [hev] with t ht
  exact ⟨ht.1.1,ht.2,ht.1.2⟩

end OAI.Analysis.PDE.Schauder
