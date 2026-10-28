import OAI.Analysis.PDE.Concentration.Cylinder.Lower
import OAI.Analysis.PDE.Concentration.LogLoss
import OAI.Analysis.PDE.Concentration.TimeTrace

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Filter Laplacian InnerProductSpace
open scoped ContDiff Topology

/-- Deterministic cylinder concentration with the cubic logarithmic loss.
Every input is a local smoothness, positivity, or Laplacian condition; the
radial propagation and the angular/time mixing are proved above. -/
theorem exists_cylinder_concentration_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : ℝ), 0 < ρ → 2 * ρ ≤ 1 → ∀ f : CylinderSpace → ℝ,
      ContDiffOn ℝ ∞ f (cylinderAnnulus (ρ / 2)) →
      (∀ x ∈ cylinderAnnulus (ρ / 2), 0 ≤ f x) →
      (∀ x ∈ cylinderAnnulus (ρ / 2), Δ f x ≤ 0) → ∀ θ : ℝ,
      (∫ t in (1 : ℝ)..2, cylinderAngularAverage f t ρ) ≤
        C * (1 + |Real.log ρ|) ^ 3 * f (cylinderPoint 0 (2 * ρ) θ) := by
  obtain ⟨D, hD, hlower⟩ := exists_cylinder_logarithmic_lower_constant
  let C := 2 * (8 * D / (Real.log 3 * Real.log 2) * (Real.log 3 + 1) ^ 2)
  have hp : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hq : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ρ hρ hρ2 f hf hn hΔ θ
  have hρ1 : ρ < 1 := by linarith
  have hv : 0 ≤ f (cylinderPoint 0 (2 * ρ) θ) := hn _
    (cylinderPoint_mem_annulus (by positivity) (by linarith) (by linarith))
  have hweighted := logarithmic_factors_cubic_upper hρ hρ1 hD.le hv
    (hlower ρ hρ hρ2 f hf hn hΔ θ)
  have hKU : cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ ρ ⊆
      cylinderAnnulus (ρ / 2) := by
    intro x hx
    exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
  have htime := cylinderTimeTrace_le_average_on (isOpen_cylinderAnnulus (ρ / 2)) hf hρ.le
    hKU (fun x hx => hn x (hKU hx))
  dsimp [C]
  nlinarith

/-- Source radii: the initial point is at transverse radius `4a`, while
the full later cylinder has radius `2a`. -/
theorem exists_source_cylinder_concentration_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (a : ℝ), 0 < a → 4 * a ≤ 1 → ∀ f : CylinderSpace → ℝ,
      ContDiffOn ℝ ∞ f (cylinderAnnulus a) →
      (∀ x ∈ cylinderAnnulus a, 0 ≤ f x) →
      (∀ x ∈ cylinderAnnulus a, Δ f x ≤ 0) → ∀ θ : ℝ,
      (∫ t in (1 : ℝ)..2, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        f (cylinderPoint t (2 * a) φ)) ≤
        C * (1 + |Real.log (2 * a)|) ^ 3 * f (cylinderPoint 0 (4 * a) θ) := by
  obtain ⟨C, hC, hbound⟩ := exists_cylinder_concentration_constant
  refine ⟨C, hC, ?_⟩
  intro a ha ha4 f hf hn hΔ θ
  have hrad : 2 * (2 * a) = 4 * a := by ring
  have hhalf : (2 * a) / 2 = a := by ring
  have hf' : ContDiffOn ℝ ∞ f (cylinderAnnulus ((2 * a) / 2)) := by simpa only [hhalf] using hf
  have hn' : ∀ x ∈ cylinderAnnulus ((2 * a) / 2), 0 ≤ f x := by simpa only [hhalf] using hn
  have hΔ' : ∀ x ∈ cylinderAnnulus ((2 * a) / 2), Δ f x ≤ 0 := by simpa only [hhalf] using hΔ
  simpa only [hrad, cylinderAngularAverage] using
    hbound (2 * a) (by positivity) (by linarith) f hf' hn' hΔ' θ

end OAI.Analysis.PDE.Concentration
