import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactFourier
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FrequencyCutoff

/-! # Lp Localization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization.CM.Construction

noncomputable section

section

/-! Restriction and zero extension for the actual L² spaces in the local compactness proof. -/

open _root_.MeasureTheory Filter Set
open scoped ENNReal

variable {α F : Type*} [NormedAddCommGroup F] {s : Set α}

def subtypeZeroExtension (f : s → F) : α → F := Function.extend Subtype.val f 0

theorem subtypeZeroExtension_apply_mem (f : s → F) {x : α} (hx : x ∈ s) :
    subtypeZeroExtension f x = f ⟨x, hx⟩ :=
  Subtype.val_injective.extend_apply f 0 ⟨x, hx⟩

theorem subtypeZeroExtension_apply_notMem (f : s → F) {x : α} (hx : x ∉ s) :
    subtypeZeroExtension f x = 0 := by
  apply Function.extend_apply'
  rintro ⟨y, rfl⟩
  exact hx y.property

theorem subtypeZeroExtension_support (f : s → F) :
    Function.support (subtypeZeroExtension f) ⊆ s := by
  intro x hx
  by_contra h
  exact hx (subtypeZeroExtension_apply_notMem f h)

theorem subtypeZeroExtension_comp (f : s → F) :
    subtypeZeroExtension f ∘ Subtype.val = f :=
  Function.extend_comp Subtype.val_injective f 0

variable [MeasurableSpace α] (μ : Measure α)

theorem subtypeZeroExtension_eLpNorm (hs : MeasurableSet s) (p : ℝ≥0∞) (f : s → F) :
    eLpNorm (subtypeZeroExtension f) p μ =
      eLpNorm f p (μ.comap (Subtype.val : s → α)) := by
  have hi : s.indicator (subtypeZeroExtension f) = subtypeZeroExtension f :=
    Set.indicator_eq_self.mpr (subtypeZeroExtension_support f)
  calc
    _ = eLpNorm (s.indicator (subtypeZeroExtension f)) p μ := by rw [hi]
    _ = eLpNorm (subtypeZeroExtension f) p (μ.restrict s) :=
      eLpNorm_indicator_eq_eLpNorm_restrict hs
    _ = eLpNorm f p (μ.comap (Subtype.val : s → α)) := by
      rw [← map_comap_subtype_coe hs μ,
        (MeasurableEmbedding.subtype_coe hs).eLpNorm_map_measure, subtypeZeroExtension_comp]

theorem subtypeZeroExtension_memLp (hs : MeasurableSet s)
    (f : Lp F 2 (μ.comap (Subtype.val : s → α))) :
    MemLp (subtypeZeroExtension f) 2 μ := by
  change eLpNorm (subtypeZeroExtension f) 2 μ < ∞
  rw [subtypeZeroExtension_eLpNorm μ hs]
  exact Lp.memLp f

theorem subtypeZeroExtension_ae_eq (hs : MeasurableSet s) {f g : s → F}
    (hfg : f =ᵐ[μ.comap (Subtype.val : s → α)] g) :
    subtypeZeroExtension f =ᵐ[μ] subtypeZeroExtension g := by
  apply ae_of_ae_restrict_of_ae_restrict_compl s
  · rw [ae_restrict_iff_subtype hs]
    filter_upwards [hfg] with x hx
    simpa only [subtypeZeroExtension_apply_mem _ x.property] using hx
  · filter_upwards [ae_restrict_mem hs.compl] with x hx
    rw [subtypeZeroExtension_apply_notMem _ hx, subtypeZeroExtension_apply_notMem _ hx]

omit [MeasurableSpace α] in
theorem subtypeZeroExtension_add (f g : s → F) :
    subtypeZeroExtension (f + g) = subtypeZeroExtension f + subtypeZeroExtension g := by
  ext x
  by_cases hx : x ∈ s
  · simp only [Pi.add_apply, subtypeZeroExtension_apply_mem _ hx]
  · simp only [Pi.add_apply, subtypeZeroExtension_apply_notMem _ hx, add_zero]

variable [NormedSpace ℂ F]

omit [MeasurableSpace α] in
theorem subtypeZeroExtension_smul (c : ℂ) (f : s → F) :
    subtypeZeroExtension (c • f) = c • subtypeZeroExtension f := by
  ext x
  by_cases hx : x ∈ s
  · simp only [Pi.smul_apply, subtypeZeroExtension_apply_mem _ hx]
  · simp only [Pi.smul_apply, subtypeZeroExtension_apply_notMem _ hx, smul_zero]

/-- Zero extension is a linear isometry for the genuine subtype measure. -/
def lpSubtypeZeroExtension (hs : MeasurableSet s) :
    Lp F 2 (μ.comap (Subtype.val : s → α)) →ₗᵢ[ℂ] Lp F 2 μ where
  toFun f := (subtypeZeroExtension_memLp μ hs f).toLp _
  map_add' f g := by
    apply Lp.ext
    refine (subtypeZeroExtension_memLp μ hs (f + g)).coeFn_toLp.trans ?_
    refine (subtypeZeroExtension_ae_eq μ hs (Lp.coeFn_add f g)).trans ?_
    rw [subtypeZeroExtension_add]
    exact ((subtypeZeroExtension_memLp μ hs f).coeFn_toLp.add
      (subtypeZeroExtension_memLp μ hs g).coeFn_toLp).symm.trans (Lp.coeFn_add _ _).symm
  map_smul' c f := by
    apply Lp.ext
    refine (subtypeZeroExtension_memLp μ hs (c • f)).coeFn_toLp.trans ?_
    refine (subtypeZeroExtension_ae_eq μ hs (Lp.coeFn_smul c f)).trans ?_
    rw [subtypeZeroExtension_smul]
    exact ((subtypeZeroExtension_memLp μ hs f).coeFn_toLp.const_smul c).symm.trans
      (Lp.coeFn_smul c _).symm
  norm_map' f := by
    change ‖(subtypeZeroExtension_memLp μ hs f).toLp _‖ = ‖f‖
    rw [Lp.norm_def, eLpNorm_congr_ae (subtypeZeroExtension_memLp μ hs f).coeFn_toLp,
      subtypeZeroExtension_eLpNorm μ hs, Lp.norm_def]

theorem lpSubtypeZeroExtension_coeFn (hs : MeasurableSet s)
    (f : Lp F 2 (μ.comap (Subtype.val : s → α))) :
    lpSubtypeZeroExtension μ hs f =ᵐ[μ] subtypeZeroExtension f :=
  (subtypeZeroExtension_memLp μ hs f).coeFn_toLp

/-- Restriction to a measure restriction is complex linear and contractive. -/
def lpMeasureRestriction (s : Set α) : Lp F 2 μ →L[ℂ] Lp F 2 (μ.restrict s) :=
  LinearMap.mkContinuous
    { toFun := fun f => ((Lp.memLp f).restrict s).toLp f
      map_add' := fun f g => by
        apply Lp.ext
        refine ((Lp.memLp (f + g)).restrict s).coeFn_toLp.trans ?_
        have h : (f + g : Lp F 2 μ) =ᵐ[μ.restrict s] (fun x => f x + g x) :=
          ae_restrict_of_ae (Lp.coeFn_add f g)
        refine h.trans ?_
        exact (((Lp.memLp f).restrict s).coeFn_toLp.add
          ((Lp.memLp g).restrict s).coeFn_toLp).symm.trans (Lp.coeFn_add _ _).symm
      map_smul' := fun c f => by
        apply Lp.ext
        refine ((Lp.memLp (c • f)).restrict s).coeFn_toLp.trans ?_
        have h : (c • f : Lp F 2 μ) =ᵐ[μ.restrict s] (fun x => c • f x) :=
          ae_restrict_of_ae (Lp.coeFn_smul c f)
        refine h.trans ?_
        exact (((Lp.memLp f).restrict s).coeFn_toLp.const_smul c).symm.trans
          (Lp.coeFn_smul c _).symm }
    1 (fun f => by
      change ‖((Lp.memLp f).restrict s).toLp f‖ ≤ 1 * ‖f‖
      rw [one_mul, Lp.norm_def,
        eLpNorm_congr_ae ((Lp.memLp f).restrict s).coeFn_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.memLp f).ne (eLpNorm_mono_measure _ Measure.restrict_le_self))

theorem lpMeasureRestriction_coeFn (s : Set α) (f : Lp F 2 μ) :
    lpMeasureRestriction μ s f =ᵐ[μ.restrict s] f :=
  ((Lp.memLp f).restrict s).coeFn_toLp

theorem lpMeasureRestriction_norm_le (s : Set α) (f : Lp F 2 μ) :
    ‖lpMeasureRestriction μ s f‖ ≤ ‖f‖ := by
  change ‖((Lp.memLp f).restrict s).toLp f‖ ≤ ‖f‖
  rw [Lp.norm_def, eLpNorm_congr_ae ((Lp.memLp f).restrict s).coeFn_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).ne (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- Restriction from the ambient measure space to its measurable subtype. -/
def lpSubtypeRestriction (hs : MeasurableSet s) :
    Lp F 2 μ →L[ℂ] Lp F 2 (μ.comap (Subtype.val : s → α)) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (Subtype.val : s → α)
    ⟨measurable_subtype_coe, map_comap_subtype_coe hs μ⟩).toContinuousLinearMap.comp
    (lpMeasureRestriction μ s)

theorem lpSubtypeRestriction_coeFn (hs : MeasurableSet s) (f : Lp F 2 μ) :
    lpSubtypeRestriction μ hs f =ᵐ[μ.comap (Subtype.val : s → α)]
      (fun x : s => f x.val) := by
  refine (Lp.coeFn_compMeasurePreserving (lpMeasureRestriction μ s f)
    ⟨measurable_subtype_coe, map_comap_subtype_coe hs μ⟩).trans ?_
  exact (ae_restrict_iff_subtype hs).mp (lpMeasureRestriction_coeFn μ s f)

theorem lpSubtypeRestriction_norm_le (hs : MeasurableSet s) (f : Lp F 2 μ) :
    ‖lpSubtypeRestriction μ hs f‖ ≤ ‖f‖ := by
  change ‖Lp.compMeasurePreserving Subtype.val
    ⟨measurable_subtype_coe, map_comap_subtype_coe hs μ⟩ (lpMeasureRestriction μ s f)‖ ≤ ‖f‖
  rw [Lp.norm_compMeasurePreserving]
  exact lpMeasureRestriction_norm_le μ s f

/-- Restricting and extending by zero is the usual measurable cutoff. -/
theorem lpSubtype_localization_coeFn (hs : MeasurableSet s) (f : Lp F 2 μ) :
    lpSubtypeZeroExtension μ hs (lpSubtypeRestriction μ hs f) =ᵐ[μ] s.indicator f := by
  refine (lpSubtypeZeroExtension_coeFn μ hs _).trans ?_
  refine (subtypeZeroExtension_ae_eq μ hs (lpSubtypeRestriction_coeFn μ hs f)).trans ?_
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ s
  · rw [subtypeZeroExtension_apply_mem _ hx, Set.indicator_of_mem hx]
  · rw [subtypeZeroExtension_apply_notMem _ hx, Set.indicator_of_notMem hx]

end

/-! L² control of sharp Fourier truncations by the actual H¹ norm. -/

open FourierTransform TemperedDistribution _root_.MeasureTheory Filter
open scoped SchwartzMap BoundedContinuousFunction ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- An L² Fourier multiplier agrees almost everywhere with multiplication of Fourier transforms. -/
theorem fourierMultiplier_l2_fourier_coeFn {g : E → ℂ}
    (hg : g.HasTemperateGrowth) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (f w : Lp F 2 (volume : Measure E))
    (hw : (w : 𝓢'(E, F)) = fourierMultiplierCLM F g (f : 𝓢'(E, F))) :
    (𝓕 w : Lp F 2 (volume : Measure E)) =ᵐ[volume] (fun x => g x • (𝓕 f) x) := by
  let G : E →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup g hg.1.continuous C hC
  let m : Lp ℂ ⊤ (volume : Measure E) := G.memLp_top.toLp _
  have heq : 𝓕 w = m • 𝓕 f := by
    apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := F) (μ := (volume : Measure E)) (p := 2)))
    change ((𝓕 w : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) =
      ((m • 𝓕 f : Lp F 2 (volume : Measure E)) : 𝓢'(E, F))
    rw [← Lp.fourier_toTemperedDistribution_eq, hw, fourierMultiplierCLM_apply,
      fourier_fourierInv_eq, Lp.fourier_toTemperedDistribution_eq]
    exact (Lp.toTemperedDistribution_smul_eq hg G.memLp_top (𝓕 f)).symm
  rw [heq]
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) m (𝓕 f),
    G.memLp_top.coeFn_toLp] with x hx hm
  rw [hx]
  change m x • (𝓕 f) x = _
  rw [show m x = G x from hm]
  rfl

/-- Sharp truncation to radius 2R has the same vanishing tail estimate as the smooth cutoff. -/
theorem fourier_sharp_tail_bound {R : ℝ} (hR : 0 < R)
    (f : Lp F 2 (volume : Measure E)) (hf : MemSobolev 1 2 (f : 𝓢'(E, F))) :
    ‖f - 𝓕⁻ (lpSubtypeZeroExtension volume (Metric.isClosed_closedBall.measurableSet)
      (lpSubtypeRestriction volume (Metric.isClosed_closedBall.measurableSet)
        (s := Metric.closedBall (0 : E) (2 * R)) (𝓕 f)))‖ ≤
      R⁻¹ * Bounds.CM.Construction.sobolevNorm E F 1 ⟨(f : 𝓢'(E, F)), hf⟩ := by
  let χ : E → ℂ := fun x => (FrequencyCutoff.CM.Construction.frequencyCutoff (E := E) hR x : ℂ)
  have hχ : χ.HasTemperateGrowth := FrequencyCutoff.CM.Construction.frequencyCutoff_temperate hR
  have ht : (fun x => 1 - χ x).HasTemperateGrowth := by fun_prop
  have htb : ∀ x, ‖1 - χ x‖ ≤ 1 := by
    intro x
    change ‖1 - (FrequencyCutoff.CM.Construction.frequencyCutoff (E := E) hR x : ℂ)‖ ≤ 1
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (FrequencyCutoff.CM.Construction.frequencyCutoff (E := E) hR).le_one)]
    linarith [(FrequencyCutoff.CM.Construction.frequencyCutoff (E := E) hR).nonneg' x]
  obtain ⟨w, hw, hn⟩ := FrequencyCutoff.CM.Construction.frequencyCutoff_tail_l2_bound hR
    (⟨(f : 𝓢'(E, F)), hf⟩ : Bounds.CM.Construction.sobolevDistributionSubmodule E F 1)
  have hw' : (w : 𝓢'(E, F)) = fourierMultiplierCLM F (fun x => 1 - χ x) (f : 𝓢'(E, F)) := by
    rw [hw]
    change (f : 𝓢'(E, F)) - fourierMultiplierCLM F χ (f : 𝓢'(E, F)) =
      fourierMultiplierCLM F ((fun _ : E => (1 : ℂ)) - χ) (f : 𝓢'(E, F))
    rw [FrequencyCutoff.CM.Construction.fourierMultiplier_sub (by fun_prop) hχ, fourierMultiplierCLM_const,
      one_smul, ContinuousLinearMap.id_apply]
  have hwae := fourierMultiplier_l2_fourier_coeFn ht htb f w hw'
  let loc := lpSubtypeZeroExtension volume Metric.isClosed_closedBall.measurableSet
    (lpSubtypeRestriction volume Metric.isClosed_closedBall.measurableSet
      (s := Metric.closedBall (0 : E) (2 * R)) (𝓕 f))
  have hnorm : ‖𝓕 f - loc‖ ≤ ‖𝓕 w‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (𝓕 f) loc, hwae,
      lpSubtype_localization_coeFn volume (s := Metric.closedBall (0 : E) (2 * R))
        Metric.isClosed_closedBall.measurableSet (𝓕 f)] with x hx hwx hlx
    rw [hx]
    change ‖(𝓕 f) x - loc x‖ ≤ _
    rw [show loc x = (Metric.closedBall (0 : E) (2 * R)).indicator
      (fun z : E => (𝓕 f : Lp F 2 (volume : Measure E)) z) x from hlx, hwx]
    by_cases hxb : x ∈ Metric.closedBall (0 : E) (2 * R)
    · rw [Set.indicator_of_mem hxb, sub_self, norm_zero]
      positivity
    · rw [Set.indicator_of_notMem hxb, sub_zero]
      have hz : FrequencyCutoff.CM.Construction.frequencyCutoff (E := E) hR x = 0 := by
        apply ContDiffBump.zero_of_le_dist
        change 2 * R ≤ dist x 0
        exact (not_le.mp hxb).le
      change ‖(𝓕 f) x‖ ≤ ‖(1 - (FrequencyCutoff.CM.Construction.frequencyCutoff (E := E) hR x : ℂ)) • (𝓕 f) x‖
      rw [hz, Complex.ofReal_zero, sub_zero, one_smul]
  have hnorm' : ‖f - 𝓕⁻ loc‖ = ‖𝓕 f - loc‖ := by
    rw [← Lp.norm_fourier_eq]
    change ‖(Lp.fourierTransformₗᵢ E F) (f - 𝓕⁻ loc)‖ = _
    rw [map_sub]
    change ‖𝓕 f - 𝓕 (𝓕⁻ loc)‖ = _
    rw [fourier_fourierInv_eq]
  change ‖f - 𝓕⁻ loc‖ ≤ _
  rw [hnorm']
  exact hnorm.trans (by simpa only [Lp.norm_fourier_eq] using hn)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization.CM.Construction
