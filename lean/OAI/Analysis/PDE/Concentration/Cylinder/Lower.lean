import OAI.Analysis.PDE.Concentration.EscapeFunction
import OAI.Analysis.PDE.Concentration.OuterTrace
import OAI.Analysis.PDE.Concentration.LocalCylinder

namespace OAI.Analysis.PDE.Concentration

open Set Filter Laplacian InnerProductSpace
open scoped ContDiff Topology

noncomputable def cylinderAnnulus (a : ℝ) : Set CylinderSpace :=
  {x | a < ‖(cylinderComplexEquiv x).2‖ ∧ ‖(cylinderComplexEquiv x).2‖ < 4}

theorem isOpen_cylinderAnnulus (a : ℝ) : IsOpen (cylinderAnnulus a) :=
  (isOpen_Ioi.preimage continuous_cylinderComplexCoordinate.norm).inter
    (isOpen_Iio.preimage continuous_cylinderComplexCoordinate.norm)

theorem cylinderPoint_mem_annulus {a t r θ : ℝ} (hr : 0 ≤ r) (har : a < r) (hr4 : r < 4) :
    cylinderPoint t r θ ∈ cylinderAnnulus a := by
  change a < ‖(cylinderComplexEquiv (cylinderPoint t r θ)).2‖ ∧
    ‖(cylinderComplexEquiv (cylinderPoint t r θ)).2‖ < 4
  simpa only [cylinderComplexEquiv_point, Complex.norm_polarCoord_symm, abs_of_nonneg hr]
    using And.intro har hr4

/-- The two logarithmic propagation factors are derived from the PDE:
radial averaging, outer-annulus mixing, and the inner escape comparison. -/
theorem exists_cylinder_logarithmic_lower_constant : ∃ D : ℝ, 0 < D ∧
    ∀ (ρ : ℝ), 0 < ρ → 2 * ρ ≤ 1 → ∀ f : CylinderSpace → ℝ,
      ContDiffOn ℝ ∞ f (cylinderAnnulus (ρ / 2)) →
      (∀ x ∈ cylinderAnnulus (ρ / 2), 0 ≤ f x) →
      (∀ x ∈ cylinderAnnulus (ρ / 2), Δ f x ≤ 0) → ∀ θ : ℝ,
      cylinderAverage f ρ * (Real.log 3 / (4 * (Real.log 3 - Real.log ρ))) *
        (Real.log 2 / (2 * (-Real.log ρ))) ≤ D * f (cylinderPoint 0 (2 * ρ) θ) := by
  obtain ⟨D, hD, hmix⟩ := exists_outer_trace_constant
  refine ⟨D, hD, ?_⟩
  intro ρ hρ hρ2 f hf hn hΔ θ
  have hρ1 : ρ < 1 := by linarith
  have hOU : outerAnnulus ⊆ cylinderAnnulus (ρ / 2) := by
    intro x hx
    exact ⟨by dsimp [outerAnnulus] at hx; linarith [hx.1], hx.2⟩
  have hKU : cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ 1 ⊆
      cylinderAnnulus (ρ / 2) := by
    intro x hx
    exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
  have hmean : 0 ≤ cylinderAverage f 1 := by
    apply cylinderAverage_nonneg
    intro t ht θ hθ
    exact hn _ (cylinderPoint_mem_annulus (by norm_num) (by linarith) (by norm_num))
  have hescape := cylinder_escape_lower hρ hρ2 (div_nonneg hmean hD.le)
    (isOpen_cylinderAnnulus (ρ / 2)) hKU hf
    (fun x hx => hn x (hKU hx)) (fun x hx => hΔ x (hKU hx))
    (m := cylinderAverage f 1 / D) (fun x hx hr => by
      apply (div_le_iff₀ hD).mpr
      have hx' : x ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2 :=
        ⟨hx.1, by change ‖(cylinderComplexEquiv x).2‖ ∈ Icc (1 : ℝ) 2; rw [hr]; norm_num⟩
      simpa only [mul_comm] using hmix f (hf.mono hOU)
        (fun y hy => hn y (hOU hy)) (fun y hy => hΔ y (hOU hy)) x hx') θ
  have hprop := cylinderAverage_logarithmic_lower_on (isOpen_cylinderAnnulus (ρ / 2))
    hf hρ hρ1
    (fun r hr t ht θ hθ => cylinderPoint_mem_annulus (by linarith [hr.1])
      (by linarith [hr.1]) (by linarith [hr.2]))
    (fun r hr t ht θ hθ => hn _ (cylinderPoint_mem_annulus (by linarith [hr.1])
      (by linarith [hr.1]) (by linarith [hr.2])))
    (fun r hr t ht θ hθ => hΔ _ (cylinderPoint_mem_annulus (by linarith [hr.1])
      (by linarith [hr.1]) (by linarith [hr.2])))
  have hB : 0 ≤ Real.log 2 / (2 * (-Real.log ρ)) := by
    apply div_nonneg (Real.log_nonneg (by norm_num))
    exact mul_nonneg (by norm_num) (neg_nonneg.mpr (Real.log_nonpos hρ.le hρ1.le))
  have h1 := mul_le_mul_of_nonneg_right hprop hB
  have h2 := mul_le_mul_of_nonneg_left hescape hD.le
  have he : D * (cylinderAverage f 1 / D * (Real.log 2 / (2 * (-Real.log ρ)))) =
      cylinderAverage f 1 * (Real.log 2 / (2 * (-Real.log ρ))) := by
    field_simp
  rw [he] at h2
  exact h1.trans h2

end OAI.Analysis.PDE.Concentration
