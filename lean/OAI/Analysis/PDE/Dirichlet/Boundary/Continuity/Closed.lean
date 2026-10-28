import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Method
import OAI.Analysis.PDE.Dirichlet.Boundary.InverseCompactness
import OAI.Analysis.PDE.Dirichlet.SmoothPeriodicExtensionPath

noncomputable section
open Set Filter Module
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace (n+1) 4
local instance continuityClosedFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance continuityClosedFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance continuityClosedSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance continuityClosedSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The precise regularity conclusion needed in the closedness step.
It concerns the already constructed actual Banach limit. -/
def HasC4PathLimits
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) : Prop :=
  ∀ {s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁} {t : ℝ}
    (L : BanachPathLimit e lat r B₀ F₀ F₁ hΩK (d.exponent/2) s t),
    ContDiffOn ℝ 4 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) {x | r x ≤ 0}

theorem InteriorThirdPathData.sequentially_closed_of_C4_limits
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (hfour : HasC4PathLimits e lat d)
    (s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hlim : Tendsto (fun k => (s k).t) atTop (𝓝 t)) :
    SmoothPathSolvable e lat r B₀ F₀ F₁ t := by
  obtain ⟨L,_⟩ := OAI.Analysis.PDE.Dirichlet.InteriorThirdPathData.exists_banach_limit_with_norm_convergence
    (n := n) (hΩK := hΩK) e lat hK d (hr.of_le (by simp)) hB₀ hF₀ hF₁
    hrper hBper hbounded hreg hpos₀ hpos₁ s ht hlim
  obtain ⟨S,hS,_⟩ := L.exists_smoothPathSolution_of_closed_contDiff
    (by omega) e lat hK hr hrper hbounded hreg hB₀ hBper ht (hfour L)
  exact ⟨S,hS⟩

end OAI.Analysis.PDE.Dirichlet
