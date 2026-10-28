import OAI.RepresentationTheory.Weil.Local.CompactApproximation
import OAI.RepresentationTheory.Weil.Local.Limits

/-! # Nonarchimedean Haar -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanHaar.Construction

noncomputable section

section

/-! Plancherel for arbitrary compact indicators over a nonarchimedean local field. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology ENNReal

theorem fourierIntegral_sub
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (μ : Measure (FunctionsMetaplectic.Construction.Position k n))
    {f g : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ (f - g) = FunctionsMetaplectic.Construction.fourierIntegral ψ μ f - FunctionsMetaplectic.Construction.fourierIntegral ψ μ g := by
  have heq : f - g = f + (-1 : ℂ) • g := by ext x; simp [sub_eq_add_neg]
  rw [heq]
  funext x
  rw [FunctionsMetaplectic.Construction.fourierIntegral_add ψ μ f ((-1 : ℂ) • g) x
    (FourierTools.Construction.fourierKernel_integrable ψ hu hc μ hf x)
    (FourierTools.Construction.fourierKernel_integrable ψ hu hc μ (hg.smul (-1)) x), FunctionsMetaplectic.Construction.fourierIntegral_smul]
  simp [sub_eq_add_neg]

theorem nonarchimedean_indicator_plancherel
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧
      (∀ f : FunctionsMetaplectic.Construction.Position k n → ℂ, IsLocallyConstant f → HasCompactSupport f → ∀ x,
        FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) x = (c : ℂ) * f (-x)) ∧
      ∀ K : Set (FunctionsMetaplectic.Construction.Position k n), IsCompact K →
        MemLp (FunctionsMetaplectic.Construction.fourierIntegral ψ μ (K.indicator (fun _ => (1 : ℂ)))) 2 μ ∧
        (∫ x, ‖FunctionsMetaplectic.Construction.fourierIntegral ψ μ (K.indicator (fun _ => (1 : ℂ))) x‖ ^ 2 ∂μ) = c * μ.real K := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  obtain ⟨c, hcpos, hspec⟩ :=
    NonarchimedeanFourier.Construction.nonarchimedean_fourier_square_and_plancherel hNondiscrete n ψ hu hc hn μ
  refine ⟨c, hcpos, fun f hf hs => (hspec f hf hs).1, fun K hK => ?_⟩
  let f : FunctionsMetaplectic.Construction.Position k n → ℂ := K.indicator (fun _ => 1)
  have hf : MemLp f 2 μ := memLp_indicator_const 2 hK.measurableSet 1 (Or.inr hK.measure_ne_top)
  obtain ⟨L, g, hL, hKL, hgj, hpoint⟩ := CompactApproximation.Construction.compact_indicator_locallyConstant_approximation hK
  have hgs (j : ℕ) : HasCompactSupport (g j) :=
    hL.of_isClosed_subset (isClosed_tsupport _) (hgj j).2.1
  have hgm (j : ℕ) : MemLp (g j) 2 μ :=
    (hgj j).1.continuous.memLp_of_hasCompactSupport (hgs j)
  have hgi (j : ℕ) : Integrable (g j) μ :=
    (hgj j).1.continuous.integrable_of_hasCompactSupport (hgs j)
  have hFm (j : ℕ) : MemLp (FunctionsMetaplectic.Construction.fourierIntegral ψ μ (g j)) 2 μ :=
    FunctionsMetaplectic.Construction.schwartzBruhat_memLp μ 2 (CompactCharacter.Construction.nonarchimedean_fourier_mem hNondiscrete ψ hu hc hn μ
      ⟨g j, FunctionsMetaplectic.Construction.compact_locallyConstant_mem (hgj j).1 (hgs j)⟩)
  have hfbound (x : FunctionsMetaplectic.Construction.Position k n) : ‖f x‖ ≤ 1 := by
    by_cases hx : x ∈ K <;> simp [f, hx]
  have hzero (j : ℕ) (x : FunctionsMetaplectic.Construction.Position k n) (hx : x ∉ L) : g j x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx ((hgj j).2.1 h))
  have hflim : Tendsto (fun j => ∫ x, ‖g j x - f x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have hb : Integrable (L.indicator (fun _ => (4 : ℝ))) μ :=
      memLp_one_iff_integrable.mp
        (memLp_indicator_const 1 hL.measurableSet 4 (Or.inr hL.measure_ne_top))
    have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
      (L.indicator (fun _ => (4 : ℝ)))
      (fun j => ((hgm j).aestronglyMeasurable.sub hf.aestronglyMeasurable).norm.pow 2) hb
      (fun j => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · simpa using h
    · change ‖‖g j x - f x‖ ^ 2‖ ≤ L.indicator (fun _ => (4 : ℝ)) x
      by_cases hx : x ∈ L
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hb' : ‖g j x - f x‖ ≤ 2 := (norm_sub_le _ _).trans
          (by linarith [(hgj j).2.2 x, hfbound x])
        nlinarith [norm_nonneg (g j x - f x)]
      · have hxK : x ∉ K := fun h => hx (hKL h)
        simp [hzero j x hx, f, hxK, hx]
    · have h := ((hpoint x).sub_const (f x)).norm.pow 2
      simpa [f] using h
  have hFpoint (x : FunctionsMetaplectic.Construction.Position k n) : Tendsto (fun j => FunctionsMetaplectic.Construction.fourierIntegral ψ μ (g j) x)
      atTop (𝓝 (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x)) := by
    have hb : Integrable (L.indicator (fun _ => (1 : ℝ))) μ :=
      memLp_one_iff_integrable.mp
        (memLp_indicator_const 1 hL.measurableSet 1 (Or.inr hL.measure_ne_top))
    apply tendsto_integral_of_dominated_convergence (L.indicator (fun _ => (1 : ℝ)))
      (fun j => (FourierTools.Construction.fourierKernel_integrable ψ hu hc μ (hgi j) x).aestronglyMeasurable) hb
    · intro j
      exact Eventually.of_forall fun y => by
        by_cases hy : y ∈ L
        · simpa [hy, norm_mul, hu] using (hgj j).2.2 y
        · simp [hzero j y hy, hy]
    · exact Eventually.of_forall fun y => (hpoint y).mul_const (ψ (-FunctionsMetaplectic.Construction.dot x y))
  have hnorm (j : ℕ) : (∫ x, ‖FunctionsMetaplectic.Construction.fourierIntegral ψ μ (g j) x‖ ^ 2 ∂μ) =
      c * ∫ x, ‖g j x‖ ^ 2 ∂μ := (hspec (g j) (hgj j).1 (hgs j)).2
  have hdiff (j l : ℕ) : (∫ x, ‖FunctionsMetaplectic.Construction.fourierIntegral ψ μ (g j) x -
      FunctionsMetaplectic.Construction.fourierIntegral ψ μ (g l) x‖ ^ 2 ∂μ) = c * ∫ x, ‖g j x - g l x‖ ^ 2 ∂μ := by
    have heq := fourierIntegral_sub ψ hu hc μ (hgi j) (hgi l)
    have h := (hspec (g j - g l) ((hgj j).1.sub (hgj l).1) ((hgs j).sub (hgs l))).2
    rw [heq] at h
    exact h
  obtain ⟨hF, heq⟩ := Limits.Construction.plancherel_pass_to_limit μ hgm hFm hf hflim hFpoint c hcpos hnorm hdiff
  refine ⟨hF, heq.trans ?_⟩
  congr 1
  have hnormf : (fun x => ‖f x‖ ^ 2) = K.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ K <;> simp [f, hx]
  rw [hnormf]
  exact integral_indicator_one hK.measurableSet

end

/-! Positivity of the exact reference-set normalization at a nonarchimedean place. -/

open _root_.MeasureTheory

theorem integral_singleton_position
    {k : Type} {E : Type*} [MeasurableSpace k] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure k) (f : k → E) :
    (∫ x : FunctionsMetaplectic.Construction.Position k 1, f (x 0) ∂(Measure.pi (fun _ : Fin 1 => μ))) = ∫ x, f x ∂μ := by
  exact (measurePreserving_funUnique μ (Fin 1)).integral_comp' f

theorem fourierIntegral_singleton_position
    {k : Type} [NormedField k] [MeasurableSpace k]
    (ψ : AddChar k ℂ) (μ : Measure k) (f : k → ℂ) (x : FunctionsMetaplectic.Construction.Position k 1) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin 1 => μ)) (fun y => f (y 0)) x =
      ∫ y, f y * ψ (-(x 0 * y)) ∂μ := by
  unfold FunctionsMetaplectic.Construction.fourierIntegral
  simp only [FunctionsMetaplectic.Construction.dot, Fin.sum_univ_one]
  exact integral_singleton_position μ (fun y => f y * ψ (-(x 0 * y)))

theorem nonarchimedean_reference_scale
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ ∧
      ∀ f : FunctionsMetaplectic.Construction.Position k 1 → ℂ, IsLocallyConstant f → HasCompactSupport f → ∀ x,
        FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin 1 => (Measure.addHaar : Measure k)))
          (FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin 1 => (Measure.addHaar : Measure k))) f) x =
            (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) * f (-x) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let μ : Measure k := Measure.addHaar
  let μ₁ : Measure (FunctionsMetaplectic.Construction.Position k 1) := Measure.pi (fun _ : Fin 1 => μ)
  let : μ₁.IsAddHaarMeasure := by dsimp [μ₁, μ]; infer_instance
  obtain ⟨c, hcpos, hsquare, hplan⟩ :=
    nonarchimedean_indicator_plancherel hNondiscrete 1 ψ hu hc hn μ₁
  let K : Set k := FunctionsMetaplectic.Construction.referenceCompact k
  let K₁ : Set (FunctionsMetaplectic.Construction.Position k 1) := (fun x => x 0) ⁻¹' K
  have hK : IsCompact K := (FunctionsMetaplectic.Construction.referenceCompact k).isCompact
  have hK₁ : IsCompact K₁ := (Homeomorph.funUnique (Fin 1) k).isCompact_preimage.mpr hK
  have hμK : 0 < μ.real K := ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior μ (FunctionsMetaplectic.Construction.referenceCompact k).interior_nonempty).ne'
    hK.measure_ne_top
  have hvol : μ₁.real K₁ = μ.real K := by
    apply congrArg ENNReal.toReal
    exact (measurePreserving_funUnique μ (Fin 1)).measure_preimage hK.measurableSet.nullMeasurableSet
  have hF (x : FunctionsMetaplectic.Construction.Position k 1) :
      FunctionsMetaplectic.Construction.fourierIntegral ψ μ₁ (K₁.indicator (fun _ => (1 : ℂ))) x = FunctionsMetaplectic.Construction.referenceFourier k ψ (x 0) := by
    have hi : K₁.indicator (fun _ => (1 : ℂ)) = fun y => K.indicator (fun _ => (1 : ℂ)) (y 0) := by
      funext y
      by_cases hy : y 0 ∈ K <;> simp [K₁, hy]
    rw [hi, fourierIntegral_singleton_position, FunctionsMetaplectic.Construction.referenceFourier, ← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      by_cases hy : y ∈ K <;> simp [hy, K]
  have henergy := (hplan K₁ hK₁).2
  simp_rw [hF] at henergy
  change (∫ x : FunctionsMetaplectic.Construction.Position k 1, ‖FunctionsMetaplectic.Construction.referenceFourier k ψ (x 0)‖ ^ 2
    ∂(Measure.pi (fun _ : Fin 1 => μ))) = c * μ₁.real K₁ at henergy
  rw [integral_singleton_position μ (fun t => ‖FunctionsMetaplectic.Construction.referenceFourier k ψ t‖ ^ 2), hvol] at henergy
  have hscale : FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ = c := by
    unfold FunctionsMetaplectic.Construction.fourierHaarScaleSquared
    change (∫ ξ, ‖FunctionsMetaplectic.Construction.referenceFourier k ψ ξ‖ ^ 2 ∂μ) / μ.real K = c
    rw [henergy, mul_div_cancel_right₀ c hμK.ne']
  exact ⟨hscale.symm ▸ hcpos, hscale.symm ▸ hsquare⟩

theorem nonarchimedean_selfDualMeasure_isAddHaarMeasure
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) :
    (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
  FourierTools.Construction.selfDualMeasure_isAddHaarMeasure_of_scale_pos k ψ
    (nonarchimedean_reference_scale hNondiscrete ψ hu hc hn).1

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanHaar.Construction
