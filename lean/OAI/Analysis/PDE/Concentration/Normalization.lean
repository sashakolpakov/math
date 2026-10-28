import OAI.Analysis.PDE.Concentration.FrequencyCount

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set OAI.Analysis.Calculus.Current _root_.MeasureTheory

theorem physicalSpatialCell_volume {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    volume.real (physicalSpatialCell R) = |LinearMap.det (spatialCellMap R).toLinearMap| := by
  have h := integral_sq_physicalSpatialCell R (fun _ : Fin 1 => (0 : OAI.Analysis.Calculus.Current.SpatialSpace d))
    (fun _ : Fin 1 => (0 : Option (Fin d) → ℤ))
    (Function.injective_of_subsingleton _) (fun _ => (1 : ℂ)) (by intro j i; simp)
  simpa [finiteWave, planeWave, integral_const, measureReal_restrict_apply_univ] using h

theorem compact_angular_frequency_count {d : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d),
      (∀ j, ‖R (EuclideanSpace.single j 1)‖ ≤ 1) →
      ∀ (h : ℝ), 0 < h → h ≤ 1 → ∀ {ι : Type} [Fintype ι]
      (ω : ι → OAI.Analysis.Calculus.Current.SpatialSpace d) (m : ι → Option (Fin d) → ℤ),
      Function.Injective m → (∀ i, h • ω i ∈ K) →
      (∀ i j, inner ℝ (ω i) (R (EuclideanSpace.single j 1)) = (m i j : ℝ) * (2 * Real.pi) / 100) →
      (Fintype.card ι : ℝ) * h ^ (d + 1) ≤ C := by
  obtain ⟨D, hD⟩ := hK.isBounded.exists_norm_le
  let B := max D 0
  have hB : 0 ≤ B := le_max_right D 0
  let P := 100 * B / (2 * Real.pi)
  have hP : 0 ≤ P := div_nonneg (mul_nonneg (by norm_num) hB) (by positivity)
  refine ⟨(2 * P + 3) ^ (d + 1), pow_pos (by positivity) _, ?_⟩
  intro R hR h hh hh1 ι _ ω m hinj hfreq hm
  have hbound (i : ι) (j : Option (Fin d)) : |(m i j : ℝ)| ≤ P / h := by
    have hnorm : ‖h • ω i‖ ≤ B := (hD _ (hfreq i)).trans (le_max_left D 0)
    have hi : |inner ℝ (h • ω i) (R (EuclideanSpace.single j 1))| ≤ B :=
      (abs_real_inner_le_norm _ _).trans (by
        calc
          _ ≤ ‖h • ω i‖ * 1 := mul_le_mul_of_nonneg_left (hR j) (norm_nonneg _)
          _ ≤ B := by simpa using hnorm)
    have hp : 0 < 2 * Real.pi := by positivity
    rw [real_inner_smul_left, hm] at hi
    simp only [abs_mul, abs_div, abs_of_pos hh, abs_of_pos hp,
      abs_of_pos (by norm_num : (0 : ℝ) < 100)] at hi
    apply (le_div_iff₀ hh).mpr
    apply (le_div_iff₀ hp).mpr
    nlinarith
  simpa only [Fintype.card_option, Fintype.card_fin] using
    integer_frequency_count m hinj hP hh hh1 hbound

/-- A normalized finite Fourier series with compact semiclassical frequency
support has mean square at least a constant times `h^n`. Cell volume is kept
explicit, so the result is valid for every full lattice with bounded column
lengths, including every rotated side-100 lattice. -/
theorem compact_angular_energy_lower {d : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d),
      (∀ j, ‖R (EuclideanSpace.single j 1)‖ ≤ 1) →
      ∀ (h : ℝ), 0 < h → h ≤ 1 → ∀ {ι : Type} [Fintype ι]
      (ω : ι → OAI.Analysis.Calculus.Current.SpatialSpace d) (m : ι → Option (Fin d) → ℤ) (a : ι → ℂ),
      Function.Injective m → (∀ i, h • ω i ∈ K) →
      (∀ i j, inner ℝ (ω i) (R (EuclideanSpace.single j 1)) = (m i j : ℝ) * (2 * Real.pi) / 100) →
      (∀ b < (1 : ℝ), ∃ x, b < ‖finiteWave (fun i => (2 * Real.pi)⁻¹ • ω i) a x‖ ^ 2) →
      volume.real (physicalSpatialCell R) * h ^ (d + 1) ≤
        C * ∫ x in physicalSpatialCell R, ‖finiteWave (fun i => (2 * Real.pi)⁻¹ • ω i) a x‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := compact_angular_frequency_count hK
  refine ⟨C, hC, ?_⟩
  intro R hR h hh hh1 ι _ ω m a hinj hfreq hm hnorm
  have he := finiteWave_energy_lower (fun i => (2 * Real.pi)⁻¹ • ω i) a hh
    (hc R hR h hh hh1 ω m hinj hfreq hm) hnorm
  have hcycles (i : ι) (j : Option (Fin d)) :
      inner ℝ ((2 * Real.pi)⁻¹ • ω i) (R (EuclideanSpace.single j 1)) = (m i j : ℝ) / 100 := by
    rw [real_inner_smul_left, hm]
    field_simp
  rw [integral_sq_physicalSpatialCell R _ m hinj a hcycles, physicalSpatialCell_volume]
  convert mul_le_mul_of_nonneg_left he (abs_nonneg (LinearMap.det (spatialCellMap R).toLinearMap)) using 1 ; ring

end OAI.Analysis.PDE.Concentration
