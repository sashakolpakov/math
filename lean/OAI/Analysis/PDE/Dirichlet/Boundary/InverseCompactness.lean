import OAI.Analysis.PDE.Dirichlet.Boundary.InverseLimitExtension
import OAI.Analysis.PDE.Dirichlet.Path.BanachCompactness

noncomputable section
open Set Module Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace (n+1) 4
local instance inverseCompactFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance inverseCompactFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance inverseCompactSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseCompactSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem InteriorThirdPathData.exists_banach_limit_with_norm_convergence
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ 3 r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hslim : Tendsto (fun k => (s k).t) atTop (𝓝 t)) :
    ∃ L : BanachPathLimit e lat r B₀ F₀ F₁ hΩK (d.exponent/2) s t,
      Tendsto (fun k => OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf d.exponent_pos.le (d.jets (s (L.subsequence k))))
        atTop (𝓝 L.value) := by
  have hp (s : SmoothPathSolution e lat r B₀ F₀ F₁) :
      LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value (d.jets s))) :=
    OAI.Analysis.Normed.Function.Holder.latticePeriodic_of_value_eq (hrper.comp (fun t => t ≤ 0)) (d.jets s)
      (fun x => B₀ x+s.u x) (hBper.add s.periodic) (d.jet_value s)
  have hΦ (s : SmoothPathSolution e lat r B₀ F₀ F₁) :=
    And.intro (d.jet_norm s) (And.intro (d.jet_value s)
      (And.intro (d.jet_first s) (And.intro (d.jet_second s) (hp s))))
  obtain ⟨g,φ,hφ,hlim⟩ := exists_densityPath_banach_subsequence e lat hK hr hB₀
    hrper hBper hbounded hreg d.exponent_pos d.normBound_pos.le s d.jets hΦ
  obtain ⟨hgp,hboundary,hadmissible,hpoint⟩ := densityPath_banach_limit_properties
    e lat hr hB₀ hF₀ hF₁ hreg hpos₀ hpos₁ (fun k => s (φ k)) ht
    (hslim.comp hφ.tendsto_atTop)
    (fun k => OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf d.exponent_pos.le (d.jets (s (φ k)))) g hlim
    (fun k => d.jet_value (s (φ k))) (fun k => d.jet_second (s (φ k)))
    (fun k => hp (s (φ k)))
  exact ⟨⟨g,hgp,hboundary,hadmissible,φ,hφ,hpoint⟩,hlim⟩

end OAI.Analysis.PDE.Dirichlet
