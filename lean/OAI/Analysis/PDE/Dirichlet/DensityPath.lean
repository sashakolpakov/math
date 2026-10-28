import OAI.Analysis.PDE.Dirichlet.Periodic.LogData

open Set Module
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- The positive affine density path used in the Dirichlet continuity method. -/
def densityPath (F₀ F₁ : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  (1 - t) * F₀ x + t * F₁ x

theorem contDiff_densityPath {F₀ F₁ : E → ℝ}
    (h₀ : ContDiff ℝ 2 F₀) (h₁ : ContDiff ℝ 2 F₁) (t : ℝ) :
    ContDiff ℝ 2 (densityPath F₀ F₁ t) :=
  (contDiff_const.mul h₀).add (contDiff_const.mul h₁)

theorem contDiff_densityPath_joint {F₀ F₁ : E → ℝ}
    (h₀ : ContDiff ℝ 2 F₀) (h₁ : ContDiff ℝ 2 F₁) :
    ContDiff ℝ 2 (fun p : ℝ × E ↦ densityPath F₀ F₁ p.1 p.2) :=
  ((contDiff_const.sub contDiff_fst).mul (h₀.comp contDiff_snd)).add
    (contDiff_fst.mul (h₁.comp contDiff_snd))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem densityPath_pos {F₀ F₁ : E → ℝ} {x : E} {t : ℝ}
    (h₀ : 0 < F₀ x) (h₁ : 0 < F₁ x) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < densityPath F₀ F₁ t x := by
  dsimp [densityPath]
  by_cases h : t = 1
  · simpa [h] using h₁
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht.2 h)) h₀) (mul_nonneg ht.1 h₁.le)

omit [Fintype ι] in
theorem densityPath_periodic (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {F₀ F₁ : E → ℝ} (h₀ : LatticePeriodic e lat F₀) (h₁ : LatticePeriodic e lat F₁)
    (t : ℝ) : LatticePeriodic e lat (densityPath F₀ F₁ t) := by
  unfold densityPath
  exact (h₀.smul (1 - t)).add (h₁.smul t)

/-- Uniform lower/upper and first-derivative bounds for the complete path.
All constants precede the path parameter. -/
theorem densityPath_uniform_bounds_lattice
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r : E → ℝ} (hr : Continuous r)
    (hrper : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    {F₀ F₁ : E → ℝ} (h₀ : ContDiff ℝ 2 F₀) (h₁ : ContDiff ℝ 2 F₁)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    ∃ m U L : ℝ, 0 < m ∧ 0 < U ∧ 0 < L ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, r x ≤ 0 →
      m ≤ densityPath F₀ F₁ t x ∧ densityPath F₀ F₁ t x ≤ U ∧
      ‖fderiv ℝ (densityPath F₀ F₁ t) x‖ ≤ L := by
  obtain ⟨m₀, hm₀, hmin₀⟩ := exists_lattice_positive_lower e lat hK hr hrper hbounded hne
    h₀.continuous.continuousOn hp₀ hpos₀
  obtain ⟨m₁, hm₁, hmin₁⟩ := exists_lattice_positive_lower e lat hK hr hrper hbounded hne
    h₁.continuous.continuousOn hp₁ hpos₁
  obtain ⟨U₀, hU₀, hmax₀⟩ := exists_lattice_norm_bound e lat hK hr hrper hbounded
    h₀.continuous.continuousOn hp₀
  obtain ⟨U₁, hU₁, hmax₁⟩ := exists_lattice_norm_bound e lat hK hr hrper hbounded
    h₁.continuous.continuousOn hp₁
  obtain ⟨L₀, hL₀, hD₀⟩ := exists_lattice_norm_bound e lat hK hr hrper hbounded
    (h₀.fderiv_right (m := 1) (by norm_num)).continuous.continuousOn hp₀.fderiv
  obtain ⟨L₁, hL₁, hD₁⟩ := exists_lattice_norm_bound e lat hK hr hrper hbounded
    (h₁.fderiv_right (m := 1) (by norm_num)).continuous.continuousOn hp₁.fderiv
  refine ⟨min m₀ m₁, U₀ + U₁, L₀ + L₁, lt_min hm₀ hm₁, by positivity, by positivity, ?_⟩
  intro t ht x hx
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hl₀ := (min_le_left m₀ m₁).trans (hmin₀ x hx)
  have hl₁ := (min_le_right m₀ m₁).trans (hmin₁ x hx)
  have hu₀ : F₀ x ≤ U₀ := (le_abs_self _).trans (hmax₀ x hx)
  have hu₁ : F₁ x ≤ U₁ := (le_abs_self _).trans (hmax₁ x hx)
  refine ⟨?_, ?_, ?_⟩
  · dsimp [densityPath]
    nlinarith [mul_le_mul_of_nonneg_left hl₀ ht', mul_le_mul_of_nonneg_left hl₁ ht.1]
  · dsimp [densityPath]
    nlinarith [mul_le_mul_of_nonneg_left hu₀ ht', mul_le_mul_of_nonneg_left hu₁ ht.1,
      mul_nonneg ht.1 hU₀.le, mul_nonneg ht' hU₁.le]
  · have hd := (((h₀.differentiable (by norm_num) x).hasFDerivAt.const_smul (1 - t)).add
        ((h₁.differentiable (by norm_num) x).hasFDerivAt.const_smul t)).fderiv
    change fderiv ℝ (densityPath F₀ F₁ t) x = _ at hd
    rw [hd]
    calc
      _ ≤ ‖(1 - t) • fderiv ℝ F₀ x‖ + ‖t • fderiv ℝ F₁ x‖ := norm_add_le _ _
      _ = (1 - t) * ‖fderiv ℝ F₀ x‖ + t * ‖fderiv ℝ F₁ x‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht', abs_of_nonneg ht.1]
      _ ≤ (1 - t) * L₀ + t * L₁ := add_le_add
        (mul_le_mul_of_nonneg_left (hD₀ x hx) ht') (mul_le_mul_of_nonneg_left (hD₁ x hx) ht.1)
      _ ≤ L₀ + L₁ := by nlinarith [mul_nonneg ht.1 hL₀.le, mul_nonneg ht' hL₁.le]

/-- The second log-density bound is uniform along the whole positive affine
path. Compactness is used on parameter times fundamental cell, not pointwise
in the parameter. -/
theorem densityPath_uniform_log_second_lattice
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r : E → ℝ} (hr : Continuous r)
    (hrper : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {F₀ F₁ : E → ℝ} (h₀ : ContDiff ℝ 2 F₀) (h₁ : ContDiff ℝ 2 F₁)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    ∃ L : ℝ, 0 < L ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, r x ≤ 0 → ∀ v : E,
      -L * ‖v‖ ^ 2 ≤ deriv (deriv (fun s : ℝ ↦
        Real.log (densityPath F₀ F₁ t (x + s • v)))) 0 := by
  let C := latticeSublevelCell e lat K r
  have hC : IsCompact C := isCompact_latticeSublevelCell e lat hK hr
  let G : ℝ × E → ℝ := fun p ↦ densityPath F₀ F₁ p.1 p.2
  have hG : ContDiff ℝ 2 G := contDiff_densityPath_joint h₀ h₁
  obtain ⟨L, hL, hbound⟩ := exists_log_second_directional_bound hG
    (isCompact_Icc.prod hC : IsCompact (Icc (0 : ℝ) 1 ×ˢ C))
    (fun p hp ↦ densityPath_pos (hpos₀ p.2 hp.2.2) (hpos₁ p.2 hp.2.2) hp.1)
  refine ⟨L, hL, ?_⟩
  intro t ht x hx v
  let y := latticeRepresentative e lat x
  have hy : y ∈ C := latticeRepresentative_mem_sublevelCell e lat hrper hbounded hx
  have hraw := hbound (t, y) ⟨ht, hy⟩ (0, v)
  have hres : -L * ‖v‖ ^ 2 ≤ deriv (deriv (fun s : ℝ ↦
      Real.log (densityPath F₀ F₁ t (y + s • v)))) 0 := by
    simpa [G, Prod.norm_def, max_eq_right (norm_nonneg v)] using hraw
  have hp := densityPath_periodic e lat hp₀ hp₁ t
  have hloc (z) (hz : r z ≤ 0) :
      ContDiffAt ℝ 2 (fun w ↦ Real.log (densityPath F₀ F₁ t w)) z :=
    (contDiff_densityPath h₀ h₁ t).contDiffAt.log
      (densityPath_pos (hpos₀ z hz) (hpos₁ z hz) ht).ne'
  rw [second_deriv_line (hloc x hx)]
  rw [second_deriv_line (hloc y hy.2)] at hres
  have heq := ((hp.comp Real.log).fderiv.fderiv).representative x
  change fderiv ℝ (fderiv ℝ (fun w ↦ Real.log (densityPath F₀ F₁ t w))) y = _ at heq
  rwa [heq] at hres

end OAI.Analysis.PDE.Dirichlet
