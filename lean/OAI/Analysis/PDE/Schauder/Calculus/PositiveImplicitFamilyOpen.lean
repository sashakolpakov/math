import OAI.Analysis.PDE.Schauder.Calculus.PositiveImplicitFamily
import OAI.Analysis.PDE.Schauder.Calculus.ImplicitFamilyOpen

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
local instance positiveOpenDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance positiveOpenDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance positiveOpenSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance positiveOpenSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- A single open parameter neighborhood supports all derivatives of the
positive implicit solution, not merely each finite order on a separate neighborhood. -/
theorem ParameterJetFields.exists_positive_implicit_family_open
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b)
    {K : Set V} (hK : IsCompact K) (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hα : 0 ≤ α) (hU : IsOpen U) {z₀ : Z} (hz₀ : z₀ ∈ U) (v₀ : D)
    (hzero : C.periodicOperator J hrp hα (z₀,v₀) = 0)
    (hder : ((fderiv ℝ (C.periodicOperator J hrp hα) (z₀,v₀)).comp
      (ContinuousLinearMap.inr ℝ Z D)).IsInvertible)
    (hpos : C.PositiveAt J hα (z₀,v₀)) :
    ∃ (v : Z → D) (W : Set Z), IsOpen W ∧ z₀ ∈ W ∧ W ⊆ U ∧
      ContDiffOn ℝ ∞ v W ∧ v z₀ = v₀ ∧
      ∀ z ∈ W, C.periodicOperator J hrp hα (z,v z) = 0 ∧
        C.PositiveAt J hα (z,v z) := by
  let : Fact (IsOpen {x | r x < 0}) := ⟨isOpen_lt hr continuous_const⟩
  let N : Set (Z × D) := {p | p.1 ∈ U ∧ C.PositiveAt J hα p}
  have hN : N ∈ 𝓝 (z₀,v₀) :=
    C.eventually_positive_hessianField J hK hr hrp hbounded hα hU hz₀ v₀ hpos
  obtain ⟨v,W,hW,hW0,hv,hv0,he⟩ := exists_smooth_implicit_family_open
    (C.periodicOperator J hrp hα) z₀ v₀ (hU.preimage continuous_fst)
    (C.contDiffOn_periodicOperator J hrp hα hU) hz₀ hzero hder hN
  refine ⟨v,W,hW,hW0,fun z hz => (he z hz).1.1,hv,hv0,?_⟩
  intro z hz
  exact ⟨(he z hz).2,(he z hz).1.2⟩

end OAI.Analysis.PDE.Schauder
