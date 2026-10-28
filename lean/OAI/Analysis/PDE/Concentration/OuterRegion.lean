import OAI.Analysis.PDE.Concentration.Cylinder.Volume
import OAI.Analysis.PDE.Concentration.LocalMixing

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian
open scoped ContDiff

theorem cylinderShell_eq_image {t₀ t₁ a b : ℝ} (ha : 0 ≤ a) :
    cylinderShell t₀ t₁ a b =
      (fun p : ℝ × ℝ × ℝ => cylinderPoint p.1 p.2.1 p.2.2) ''
        (Icc t₀ t₁ ×ˢ (Icc a b ×ˢ Icc (-Real.pi) Real.pi)) := by
  ext x
  constructor
  · intro hx
    let z := (cylinderComplexEquiv x).2
    refine ⟨((cylinderComplexEquiv x).1, ‖z‖, Complex.arg z), ?_, ?_⟩
    · exact ⟨hx.1, hx.2, (Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
    · apply cylinderComplexEquiv.injective
      rw [cylinderComplexEquiv_point]
      apply Prod.ext
      · rfl
      · change Complex.polarCoord.symm (‖z‖, Complex.arg z) = z
        simpa only [Complex.polarCoord_symm_apply, Complex.ofReal_cos, Complex.ofReal_sin]
          using Complex.norm_mul_cos_add_sin_mul_I z
  · rintro ⟨⟨t, r, θ⟩, ⟨ht, hr, hθ⟩, rfl⟩
    change cylinderComplexEquiv (cylinderPoint t r θ) ∈
      Icc t₀ t₁ ×ˢ {z : ℂ | ‖z‖ ∈ Icc a b}
    rw [cylinderComplexEquiv_point]
    exact ⟨ht, by simpa only [Set.mem_ofPred_eq, Complex.norm_polarCoord_symm,
      abs_of_nonneg (ha.trans hr.1)] using hr⟩

noncomputable def outerAnnulus : Set CylinderSpace :=
  {x | 1 / 2 < ‖(cylinderComplexEquiv x).2‖ ∧ ‖(cylinderComplexEquiv x).2‖ < 4}

theorem continuous_cylinderComplexCoordinate : Continuous (fun x => (cylinderComplexEquiv x).2) := by
  simp only [cylinderComplexEquiv_apply]
  fun_prop

theorem isOpen_outerAnnulus : IsOpen outerAnnulus :=
  isOpen_Ioo.preimage continuous_cylinderComplexCoordinate.norm

theorem outerShell_ball_subset {t₀ t₁ : ℝ} {x : CylinderSpace}
    (hx : x ∈ cylinderShell t₀ t₁ 1 2) : closedBall x (7 * (1 / 64)) ⊆ outerAnnulus := by
  intro y hy
  have hxy := cylinderComplexCoordinate_dist_le y x
  have hnorm := abs_norm_sub_norm_le ((cylinderComplexEquiv y).2) ((cylinderComplexEquiv x).2)
  have hd : dist y x ≤ 7 * (1 / 64) := hy
  rw [← dist_eq_norm] at hnorm
  have hlo : (1 : ℝ) ≤ ‖(cylinderComplexEquiv x).2‖ := hx.2.1
  have hhi : ‖(cylinderComplexEquiv x).2‖ ≤ (2 : ℝ) := hx.2.2
  change 1 / 2 < ‖(cylinderComplexEquiv y).2‖ ∧ ‖(cylinderComplexEquiv y).2‖ < 4
  constructor <;> linarith [(abs_le.mp hnorm).1, (abs_le.mp hnorm).2]

/-- Uniform outer-annulus mixing, with no probabilistic or Harnack premise.
The constant depends only on the fixed time interval. -/
theorem exists_outerShell_mixing_constant (t₀ t₁ : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : CylinderSpace → ℝ, ContDiffOn ℝ ∞ f outerAnnulus →
      (∀ y ∈ outerAnnulus, 0 ≤ f y) → (∀ y ∈ outerAnnulus, Δ f y ≤ 0) →
      ∀ x ∈ cylinderShell t₀ t₁ 1 2,
        (∫ y in cylinderShell t₀ t₁ 1 2, f y) ≤ M * f x := by
  let K : Set (ℝ × ℝ × ℝ) := Icc t₀ t₁ ×ˢ (Icc 1 2 ×ˢ Icc (-Real.pi) Real.pi)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hconv : Convex ℝ K := (convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))
  have he := cylinderShell_eq_image (t₀ := t₀) (t₁ := t₁) (a := 1) (b := 2) (by norm_num)
  obtain ⟨M, hM, hm⟩ := exists_uniform_local_compact_volume_mixing hK hconv
    contDiff_cylinderPoint.continuous.continuousOn (show (0 : ℝ) < 1 / 64 by norm_num)
    isOpen_outerAnnulus (fun x hx => outerShell_ball_subset (by rw [he]; exact hx))
  refine ⟨M, hM, ?_⟩
  intro f hf hn hΔ x hx
  rw [he] at hx ⊢
  exact hm f hf hn hΔ x hx

end OAI.Analysis.PDE.Concentration
