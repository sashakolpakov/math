import OAI.Analysis.Fourier.WavePackets.Lp

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal

def translatedCube (n : ℕ) (r : ℝ) (k : Fin n → ℤ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x - integerVector k ∈ coordinateCube n r}

theorem measurableSet_translatedCube (n : ℕ) (r : ℝ) (k : Fin n → ℤ) :
    MeasurableSet (translatedCube n r k) :=
  (measurableSet_coordinateCube n r).preimage (by fun_prop)

theorem exists_translatedCube (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ k : Fin n → ℤ, x ∈ translatedCube n (1 / 2) k := by
  refine ⟨fun i => ⌊x i + 1 / 2⌋, ?_⟩
  intro i
  change |x i - (⌊x i + 1 / 2⌋ : ℝ)| ≤ 1 / 2
  have h₁ := Int.floor_le (x i + 1 / 2)
  have h₂ := Int.lt_floor_add_one (x i + 1 / 2)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem lintegral_le_tsum_translatedCube {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hu : Measurable u) :
    (∫⁻ x, u x) ≤ ∑' k : Fin n → ℤ, ∫⁻ x in translatedCube n (1 / 2) k, u x := by
  simp_rw [← lintegral_indicator (measurableSet_translatedCube n (1 / 2) _)]
  rw [← lintegral_tsum fun k => (hu.indicator (measurableSet_translatedCube n (1 / 2) k)).aemeasurable]
  apply lintegral_mono
  intro x
  obtain ⟨k, hk⟩ := exists_translatedCube n x
  calc
    u x = (translatedCube n (1 / 2) k).indicator u x := (Set.indicator_of_mem hk _).symm
    _ ≤ ∑' j : Fin n → ℤ, (translatedCube n (1 / 2) j).indicator u x :=
      ENNReal.le_tsum (f := fun j => (translatedCube n (1 / 2) j).indicator u x) k

theorem enlarged_cube_multiplicity {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (a : ℝ≥0∞) :
    (∑' k : Fin n → ℤ, (translatedCube n 5 k).indicator (fun _ => a) x) ≤
      (11 : ℝ≥0∞) ^ n * a := by
  classical
  let S : Finset (Fin n → ℤ) := Fintype.piFinset fun i => Finset.Icc (⌊x i⌋ - 5) (⌊x i⌋ + 5)
  have hS : ∀ k, x ∈ translatedCube n 5 k → k ∈ S := by
    intro k hk
    apply Fintype.mem_piFinset.mpr
    intro i
    have hi := hk i
    change |x i - (k i : ℝ)| ≤ 5 at hi
    have hl := Int.floor_le (x i)
    have hu := Int.lt_floor_add_one (x i)
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast (show (⌊x i⌋ : ℝ) - 5 ≤ k i by linarith [abs_le.mp hi])
    · have hh : k i < ⌊x i⌋ + 6 := by
        exact_mod_cast (show (k i : ℝ) < (⌊x i⌋ : ℝ) + 6 by linarith [abs_le.mp hi])
      omega
  have hcard : S.card = 11 ^ n := by
    simp [S, Fintype.card_piFinset, Int.card_Icc, show ∀ z : ℤ, z + 5 + 1 - (z - 5) = 11 by omega]
  rw [tsum_eq_sum (s := S) (fun k hk => Set.indicator_of_notMem (fun hx => hk (hS k hx)) _)]
  calc
    _ ≤ ∑ k ∈ S, a := Finset.sum_le_sum fun k _ => Set.indicator_le_self _ _ x
    _ = (11 : ℝ≥0∞) ^ n * a := by simp [hcard]

theorem tsum_lintegral_enlargedCube_le {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hu : Measurable u) :
    (∑' k : Fin n → ℤ, ∫⁻ x in translatedCube n 5 k, u x) ≤
      (11 : ℝ≥0∞) ^ n * ∫⁻ x, u x := by
  simp_rw [← lintegral_indicator (measurableSet_translatedCube n 5 _)]
  rw [← lintegral_tsum fun k => (hu.indicator (measurableSet_translatedCube n 5 k)).aemeasurable,
    ← lintegral_const_mul' _ _ (by finiteness)]
  apply lintegral_mono
  intro x
  exact enlarged_cube_multiplicity x (u x)

noncomputable def cubeSpacetimeMeasure (n : ℕ) (k : Fin n → ℤ) :
    Measure (ℝ × EuclideanSpace ℝ (Fin n)) :=
  (volume.restrict (Set.Icc (1 : ℝ) 2)).prod (volume.restrict (translatedCube n (1 / 2) k))

theorem lintegral_spacetime_le_tsum_cubes {n : ℕ}
    {u : ℝ × EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hu : Measurable u) :
    (∫⁻ q, u q ∂(volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) ≤
      ∑' k : Fin n → ℤ, ∫⁻ q, u q ∂cubeSpacetimeMeasure n k := by
  rw [lintegral_prod _ hu.aemeasurable]
  calc
    _ ≤ ∫⁻ T in Set.Icc (1 : ℝ) 2,
        ∑' k : Fin n → ℤ, ∫⁻ X in translatedCube n (1 / 2) k, u (T, X) := by
      apply lintegral_mono
      intro T
      exact lintegral_le_tsum_translatedCube (hu.comp (measurable_const.prodMk measurable_id))
    _ = _ := by
      rw [lintegral_tsum]
      · congr 1
        funext k
        exact (lintegral_prod _ hu.aemeasurable).symm
      · intro k
        exact (hu.lintegral_prod_right').aemeasurable

theorem eLpNorm_rpow_eq_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ⊤)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f p μ ^ p.toReal = ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf, ← ENNReal.rpow_mul]
  simp [ENNReal.toReal_ne_zero.mpr ⟨hp0, hptop⟩]

/-- Cubewise `Lᵖ` estimates glue globally with the explicit overlap constant
`11^(n/p)`. No partition-of-unity or unproved overlap hypothesis is needed. -/
theorem eLpNorm_le_of_cube_bounds {n : ℕ}
    {u : ℝ × EuclideanSpace ℝ (Fin n) → ℂ} (hu : Measurable u)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Measurable f)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ⊤) (A : ℝ≥0∞)
    (hlocal : ∀ k : Fin n → ℤ, eLpNorm u p (cubeSpacetimeMeasure n k) ≤
      A * eLpNorm f p (volume.restrict (translatedCube n 5 k))) :
    eLpNorm u p ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) ≤
      A * ((11 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) * eLpNorm f p volume := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hi : (∫⁻ q, ‖u q‖ₑ ^ p.toReal ∂(volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) ≤
      A ^ p.toReal * ((11 : ℝ≥0∞) ^ n * ∫⁻ x, ‖f x‖ₑ ^ p.toReal) := by
    calc
      _ ≤ ∑' k : Fin n → ℤ, ∫⁻ q, ‖u q‖ₑ ^ p.toReal ∂cubeSpacetimeMeasure n k :=
        lintegral_spacetime_le_tsum_cubes (hu.enorm.pow_const _)
      _ ≤ ∑' k : Fin n → ℤ,
          A ^ p.toReal * ∫⁻ x in translatedCube n 5 k, ‖f x‖ₑ ^ p.toReal := by
        apply ENNReal.tsum_le_tsum
        intro k
        have he := ENNReal.rpow_le_rpow (hlocal k) hp.le
        rw [eLpNorm_rpow_eq_lintegral hp0 hptop hu.aestronglyMeasurable,
          ENNReal.mul_rpow_of_nonneg _ _ hp.le,
          eLpNorm_rpow_eq_lintegral hp0 hptop hf.aestronglyMeasurable] at he
        exact he
      _ = A ^ p.toReal * ∑' k : Fin n → ℤ,
          ∫⁻ x in translatedCube n 5 k, ‖f x‖ₑ ^ p.toReal := ENNReal.tsum_mul_left
      _ ≤ _ := mul_le_mul_right
        (tsum_lintegral_enlargedCube_le (hf.enorm.pow_const _)) _
  have hroot := ENNReal.rpow_le_rpow hi (show 0 ≤ 1 / p.toReal by positivity)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one] at hroot
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hu.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf.aestronglyMeasurable]
  simpa only [mul_assoc] using hroot

end OAI.Analysis.Fourier.WavePackets
