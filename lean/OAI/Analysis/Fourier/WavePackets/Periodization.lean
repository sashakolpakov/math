import OAI.Analysis.Fourier.WavePackets.Spacetime

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ContDiff RealInnerProductSpace

/-- The standard integer lattice, realized as a discrete submodule of
Euclidean space so that lattice summation uses its Euclidean norm. -/
noncomputable def integerLattice (n : ℕ) : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)

instance (n : ℕ) : DiscreteTopology (integerLattice n) := by
  unfold integerLattice
  infer_instance

instance (n : ℕ) : IsZLattice ℝ (integerLattice n) := by
  unfold integerLattice
  infer_instance

theorem integerLattice_coordinate {n : ℕ} (k : integerLattice n) (i : Fin n) :
    ∃ m : ℤ, (m : ℝ) = (k : EuclideanSpace ℝ (Fin n)) i := by
  have hi := ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.mem_span_iff_repr_mem ℤ
    (k : EuclideanSpace ℝ (Fin n))).mp k.property i
  simpa using hi

theorem integerLattice_norm_ge_one {n : ℕ} {k : integerLattice n} (hk : k ≠ 0) :
    1 ≤ ‖(k : EuclideanSpace ℝ (Fin n))‖ := by
  have hex : ∃ i, (k : EuclideanSpace ℝ (Fin n)) i ≠ 0 := by
    by_contra! h
    apply hk
    apply Subtype.ext
    ext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  obtain ⟨m, hm⟩ := integerLattice_coordinate k i
  have hm₀ : m ≠ 0 := by intro hz; apply hi; simpa [hz] using hm.symm
  have hm₁ : (1 : ℝ) ≤ |(m : ℝ)| := by
    have : 0 < |m| := abs_pos.mpr hm₀
    exact_mod_cast (show (1 : ℤ) ≤ |m| by omega)
  calc
    (1 : ℝ) ≤ |(k : EuclideanSpace ℝ (Fin n)) i| := hm ▸ hm₁
    _ ≤ ‖(k : EuclideanSpace ℝ (Fin n))‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (k : EuclideanSpace ℝ (Fin n)) i

theorem euclidean_norm_le_of_coordinate_abs_le {n : ℕ}
    {x y : EuclideanSpace ℝ (Fin n)} (h : ∀ i, |x i| ≤ |y i|) : ‖x‖ ≤ ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg x) (norm_nonneg y)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x i)) (abs_nonneg (y i))).mpr (h i)

/-- The exact separated-copy geometry in the source: coordinate displacement
at most `5.5` and lattice period `100` yield a factor `94.5`. -/
theorem periodization_separation {n : ℕ} (z : EuclideanSpace ℝ (Fin n))
    (hz : ∀ i, |z i| ≤ (11 : ℝ) / 2) (k : integerLattice n) :
    (189 : ℝ) / 2 * ‖(k : EuclideanSpace ℝ (Fin n))‖ ≤
      ‖z + (100 : ℝ) • (k : EuclideanSpace ℝ (Fin n))‖ := by
  have hc : ∀ i, |(((189 : ℝ) / 2) • (k : EuclideanSpace ℝ (Fin n))) i| ≤
      |(z + (100 : ℝ) • (k : EuclideanSpace ℝ (Fin n))) i| := by
    intro i
    obtain ⟨m, hm⟩ := integerLattice_coordinate k i
    simp only [PiLp.smul_apply, smul_eq_mul, PiLp.add_apply, ← hm, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 189 / 2)]
    by_cases hm₀ : m = 0
    · simp [hm₀]
    · have hm₁ : (1 : ℝ) ≤ |(m : ℝ)| := by
        have : 0 < |m| := abs_pos.mpr hm₀
        exact_mod_cast (show (1 : ℤ) ≤ |m| by omega)
      have ht : 100 * |(m : ℝ)| ≤ |z i + 100 * (m : ℝ)| + |z i| := by
        calc
          _ = |(z i + 100 * (m : ℝ)) - z i| := by
            rw [add_sub_cancel_left, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
          _ ≤ _ := abs_sub _ _
      linarith [hz i]
  have hb := euclidean_norm_le_of_coordinate_abs_le hc
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 189 / 2)] using hb

/-- All nontrivial lattice copies are outside the wave cone. -/
theorem periodization_off_cone {n : ℕ} (z : EuclideanSpace ℝ (Fin n))
    (hz : ∀ i, |z i| ≤ (11 : ℝ) / 2) {k : integerLattice n} (hk : k ≠ 0) :
    3 ≤ ‖z + (100 : ℝ) • (k : EuclideanSpace ℝ (Fin n))‖ := by
  have h₁ := integerLattice_norm_ge_one hk
  have h₂ := periodization_separation z hz k
  linarith

/-- The nonzero translated kernels in the periodization remainder. -/
noncomputable def periodizationRemainderTerm {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (a : EuclideanSpace ℝ (Fin n) → ℂ)
    (h T : ℝ) (z : EuclideanSpace ℝ (Fin n)) (k : integerLattice n) : ℂ :=
  if k = 0 then 0 else semiclassicalWaveKernel μ a h T (z + (100 : ℝ) • (k : EuclideanSpace ℝ (Fin n)))

noncomputable def periodizationRemainder {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (a : EuclideanSpace ℝ (Fin n) → ℂ)
    (h T : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑' k : integerLattice n, periodizationRemainderTerm μ a h T z k

/-- Absolute convergence of the nonzero-copy series and its uniform rapid
decay. The constant is independent of displacement, time, and scale. -/
theorem periodizationRemainder_bound {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
    {a : EuclideanSpace ℝ (Fin n) → ℂ}
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : EuclideanSpace ℝ (Fin n)) (T h : ℝ),
      (∀ i, |z i| ≤ (11 : ℝ) / 2) → 0 ≤ T → T ≤ 2 → 0 < h → h ≤ 1 →
      Summable (fun k : integerLattice n => ‖periodizationRemainderTerm μ a h T z k‖) ∧
      ‖periodizationRemainder μ a h T z‖ ≤ C * h ^ N := by
  let d := Module.finrank ℤ (integerLattice n) + 1
  let M := N + d
  let w : integerLattice n → ℝ := fun k => ‖k‖⁻¹ ^ M
  have hw : Summable w := ZLattice.summable_norm_pow_inv (integerLattice n) M (by dsimp [M, d]; omega)
  obtain ⟨C, hC, hb⟩ := semiclassicalWaveKernel_off_cone (μ := μ) ha hzero hs M
  refine ⟨C * ∑' k, w k, mul_nonneg hC (tsum_nonneg fun k => by positivity), ?_⟩
  intro z T h hz hT₀ hT₁ hh hh₁
  have hbound (k : integerLattice n) :
      ‖periodizationRemainderTerm μ a h T z k‖ ≤ (C * h ^ N) * w k := by
    by_cases hk : k = 0
    · simp only [periodizationRemainderTerm, ite_eq_left hk, norm_zero]
      positivity
    · simp only [periodizationRemainderTerm, ite_eq_right hk]
      have hk₁ := integerLattice_norm_ge_one hk
      have hk₀ : 0 < ‖(k : EuclideanSpace ℝ (Fin n))‖ := lt_of_lt_of_le zero_lt_one hk₁
      have hr := periodization_separation z hz k
      have hr' : ‖(k : EuclideanSpace ℝ (Fin n))‖ ≤
          1 + ‖z + (100 : ℝ) • (k : EuclideanSpace ℝ (Fin n))‖ := by linarith
      have hp : h ^ M ≤ h ^ N := by
        dsimp [M]
        rw [pow_add]
        exact mul_le_of_le_one_right (pow_nonneg hh.le N) (pow_le_one₀ hh.le hh₁)
      calc
        _ ≤ C * h ^ M / (1 + ‖z + (100 : ℝ) • (k : EuclideanSpace ℝ (Fin n))‖) ^ M :=
          hb _ T h (periodization_off_cone z hz hk) hT₀ hT₁ hh
        _ ≤ C * h ^ N / ‖(k : EuclideanSpace ℝ (Fin n))‖ ^ M :=
          div_le_div₀ (mul_nonneg hC (pow_nonneg hh.le N))
            (mul_le_mul_of_nonneg_left hp hC) (pow_pos hk₀ M)
            (pow_le_pow_left₀ hk₀.le hr' M)
        _ = _ := by simp only [w, div_eq_mul_inv, inv_pow, Submodule.norm_coe]
  have hsbound := hw.mul_left (C * h ^ N)
  have hsnorm : Summable (fun k : integerLattice n => ‖periodizationRemainderTerm μ a h T z k‖) :=
    hsbound.of_nonneg_of_le (fun k => norm_nonneg _) hbound
  refine ⟨hsnorm, ?_⟩
  have hsum := hsnorm.of_norm.hasSum.norm_le_of_bounded hsbound.hasSum hbound
  simpa only [periodizationRemainder, tsum_mul_left, mul_assoc, mul_left_comm, mul_comm] using hsum

theorem measurable_periodizationRemainder_spacetime {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
    {a : EuclideanSpace ℝ (Fin n) → ℂ}
    (ha : Continuous a) (hs : HasCompactSupport a) (h : ℝ) :
    Measurable (fun q : ℝ × EuclideanSpace ℝ (Fin n) => periodizationRemainder μ a h q.1 q.2) := by
  apply Measurable.tsum
  intro k
  by_cases hk : k = 0
  · simp only [periodizationRemainderTerm, ite_eq_left hk]
    fun_prop
  · simp only [periodizationRemainderTerm, ite_eq_right hk]
    apply Continuous.measurable
    have hmap : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        (q.1, q.2 + (100 : ℝ) • (k : EuclideanSpace ℝ (Fin n)))) :=
      continuous_fst.prodMk (continuous_snd.add continuous_const)
    have hc : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        semiclassicalWaveKernel μ a h q.1 q.2) :=
      continuous_semiclassicalWaveKernel_spacetime (E := EuclideanSpace ℝ (Fin n))
        (μ := μ) ha hs h
    convert hc.comp hmap using 1
    rfl

/-- The centered cube with coordinate radius `r`. -/
def coordinateCube (n : ℕ) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, |x i| ≤ r}

theorem coordinateCube_displacement {n : ℕ} {X Y : EuclideanSpace ℝ (Fin n)}
    (hX : X ∈ coordinateCube n (1 / 2)) (hY : Y ∈ coordinateCube n 5) :
    ∀ i, |(X - Y) i| ≤ (11 : ℝ) / 2 := by
  intro i
  calc
    _ ≤ |X i| + |Y i| := abs_sub _ _
    _ ≤ _ := by linarith [hX i, hY i]

/-- Action of the nonzero periodized copies on an input localized to `10Q`. -/
noncomputable def periodizationError {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (a f : EuclideanSpace ℝ (Fin n) → ℂ)
    (h T : ℝ) (X : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∫ Y, periodizationRemainder μ a h T (X - Y) * f Y ∂μ

/-- The source's pointwise periodization error estimate on `Q`, with the
integrability of its defining integral included. -/
theorem periodizationError_bound {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
    {a : EuclideanSpace ℝ (Fin n) → ℂ}
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → ℂ),
      Integrable f μ → (∀ᵐ Y ∂μ, f Y ≠ 0 → Y ∈ coordinateCube n 5) →
      ∀ (X : EuclideanSpace ℝ (Fin n)) (T h : ℝ),
        X ∈ coordinateCube n (1 / 2) → 0 ≤ T → T ≤ 2 → 0 < h → h ≤ 1 →
        Integrable (fun Y => periodizationRemainder μ a h T (X - Y) * f Y) μ ∧
        ‖periodizationError μ a f h T X‖ ≤ C * h ^ N * ∫ Y, ‖f Y‖ ∂μ := by
  obtain ⟨C, hC, hb⟩ := periodizationRemainder_bound (μ := μ) ha hzero hs N
  refine ⟨C, hC, ?_⟩
  intro f hf hsupport X T h hX hT₀ hT₁ hh hh₁
  have hpoint : ∀ᵐ Y ∂μ, ‖periodizationRemainder μ a h T (X - Y) * f Y‖ ≤
      C * h ^ N * ‖f Y‖ := by
    filter_upwards [hsupport] with Y hY
    by_cases hfY : f Y = 0
    · simp [hfY]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hb (X - Y) T h (coordinateCube_displacement hX (hY hfY)) hT₀ hT₁ hh hh₁).2
        (norm_nonneg _)
  have hmeas : AEStronglyMeasurable
      (fun Y => periodizationRemainder μ a h T (X - Y) * f Y) μ :=
    (((measurable_periodizationRemainder_spacetime ha.continuous hs h).comp
      (measurable_const.prodMk (measurable_const.sub measurable_id))).aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  have hint := (hf.norm.const_mul (C * h ^ N)).mono' hmeas hpoint
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ Y, ‖periodizationRemainder μ a h T (X - Y) * f Y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ Y, C * h ^ N * ‖f Y‖ ∂μ := integral_mono_ae hint.norm (hf.norm.const_mul _) hpoint
    _ = _ := integral_const_mul _ _

end OAI.Analysis.Fourier.WavePackets
