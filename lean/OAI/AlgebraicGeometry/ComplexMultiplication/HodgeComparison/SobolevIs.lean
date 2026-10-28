import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalizedFourier
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization

/-! # Sobolev Is -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction

noncomputable section

section

/-! Local Rellich compactness for smooth functions supported in a fixed compact set. -/

open _root_.MeasureTheory FourierTransform TemperedDistribution Set _root_.Metric
open scoped SchwartzMap

/-- Uniform approximation by totally bounded images makes the original set totally bounded. -/
theorem totallyBounded_of_uniform_approximation {H : Type*} [PseudoMetricSpace H] {S : Set H}
    (h : ∀ ε > 0, ∃ T : H → H, TotallyBounded (T '' S) ∧ ∀ x ∈ S, dist x (T x) < ε) :
    TotallyBounded S := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨T, hT, hdist⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨centers, hfin, hcover⟩ := Metric.totallyBounded_iff.mp hT (ε / 2) (half_pos hε)
  refine ⟨centers, hfin, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover (mem_image_of_mem T hx))
  apply Set.mem_iUnion₂.mpr
  refine ⟨y, hy, ?_⟩
  have hclose : dist (T x) y < ε / 2 := hxy
  exact (dist_triangle x (T x) y).trans_lt (by linarith [hdist x hx])

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Sobolev norm of an actual Schwartz function. -/
def schwartzSobolevNorm (s : ℝ) (f : 𝓢(E, ℂ)) : ℝ :=
  Bounds.CM.Construction.sobolevNorm E ℂ s ⟨(f : 𝓢'(E, ℂ)), f.memSobolev⟩

theorem l2_norm_le_sobolevNorm {s : ℝ} (hs : 0 ≤ s)
    (f : Lp ℂ 2 (volume : Measure E)) (hf : MemSobolev s 2 (f : 𝓢'(E, ℂ))) :
    ‖f‖ ≤ Bounds.CM.Construction.sobolevNorm E ℂ s ⟨(f : 𝓢'(E, ℂ)), hf⟩ := by
  let u : Bounds.CM.Construction.sobolevDistributionSubmodule E ℂ s := ⟨(f : 𝓢'(E, ℂ)), hf⟩
  have hcoord : (Bounds.CM.Construction.sobolevCoordinateEquiv E ℂ 0).symm (Bounds.CM.Construction.sobolevInclusion hs u) = f := by
    apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (μ := (volume : Measure E)) (p := 2)))
    change (((Bounds.CM.Construction.sobolevCoordinateEquiv E ℂ 0).symm (Bounds.CM.Construction.sobolevInclusion hs u)) : 𝓢'(E, ℂ)) = _
    rw [Bounds.CM.Construction.sobolevCoordinateEquiv_symm_distribution, besselPotential_zero,
      ContinuousLinearMap.id_apply]
    rfl
  have h := Bounds.CM.Construction.sobolevInclusion_norm_le hs u
  change ‖(Bounds.CM.Construction.sobolevCoordinateEquiv E ℂ 0).symm (Bounds.CM.Construction.sobolevInclusion hs u)‖ ≤ _ at h
  rwa [hcoord] at h

theorem schwartz_l2_norm_le_sobolevNorm {s : ℝ} (hs : 0 ≤ s) (f : 𝓢(E, ℂ)) :
    ‖f.toLp 2 (volume : Measure E)‖ ≤ schwartzSobolevNorm s f := by
  have hf : MemSobolev s 2 ((f.toLp 2 (volume : Measure E)) : 𝓢'(E, ℂ)) := by
    rw [Lp.toTemperedDistribution_toLp_eq]
    exact f.memSobolev
  have h := l2_norm_le_sobolevNorm hs (f.toLp 2 (volume : Measure E)) hf
  simpa only [Lp.toTemperedDistribution_toLp_eq, schwartzSobolevNorm] using h

theorem finite_subtype_volume {K : Set E} (hK : IsCompact K) :
    IsFiniteMeasure ((volume : Measure E).comap (Subtype.val : K → E)) where
  measure_univ_lt_top := by
    rw [comap_subtype_coe_apply hK.measurableSet, Set.image_univ, Subtype.range_coe]
    exact hK.measure_lt_top

/-- Bounded H¹ families of smooth functions with fixed compact support have compact L² closure. -/
theorem schwartz_rellich_compact {K : Set E} (hK : IsCompact K) (C : ℝ) :
    IsCompact (closure ((fun f : 𝓢(E, ℂ) => f.toLp 2 (volume : Measure E)) ''
      {f | Function.support f ⊆ K ∧ schwartzSobolevNorm 1 f ≤ C})) := by
  let S : Set (Lp ℂ 2 (volume : Measure E)) :=
    (fun f : 𝓢(E, ℂ) => f.toLp 2 (volume : Measure E)) ''
      {f | Function.support f ⊆ K ∧ schwartzSobolevNorm 1 f ≤ C}
  have hbounded : Bornology.IsBounded S := by
    have hb : Bornology.IsBounded (Metric.closedBall (0 : Lp ℂ 2 (volume : Measure E)) C) :=
      Metric.isBounded_closedBall
    apply hb.subset
    rintro _ ⟨f, ⟨_, hnorm⟩, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (schwartz_l2_norm_le_sobolevNorm (by norm_num : (0 : ℝ) ≤ 1) f).trans hnorm
  have htotal : TotallyBounded S := by
    apply totallyBounded_of_uniform_approximation
    intro ε hε
    let R := (|C| + 1) / ε
    have hR : 0 < R := by dsimp [R]; positivity
    have hsmall : R⁻¹ * C < ε := by
      rw [inv_mul_eq_div, div_lt_iff₀ hR]
      dsimp [R]
      rw [mul_div_cancel₀ _ hε.ne']
      linarith [le_abs_self C]
    let B := Metric.closedBall (0 : E) (2 * R)
    have hB : IsCompact B := isCompact_closedBall _ _
    have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have : CompactSpace B := isCompact_iff_compactSpace.mp hB
    have := finite_subtype_volume hK
    have := finite_subtype_volume hB
    let T := LocalizedFourier.CM.Construction.localizedFourierMap hK.measurableSet hB.measurableSet
    refine ⟨T, ?_, ?_⟩
    · exact ((LocalizedFourier.CM.Construction.localizedFourierMap_isCompact hK.measurableSet hB.measurableSet
        (E := E)).isCompact_closure_image_of_bounded
        (f := T.toLinearMap) hbounded).totallyBounded.subset subset_closure
    · rintro _ ⟨f, ⟨hf, hnorm⟩, rfl⟩
      have hf' : MemSobolev 1 2 ((f.toLp 2 (volume : Measure E)) : 𝓢'(E, ℂ)) := by
        rw [Lp.toTemperedDistribution_toLp_eq]
        exact f.memSobolev
      have htail := LpLocalization.CM.Construction.fourier_sharp_tail_bound hR (f.toLp 2 (volume : Measure E)) hf'
      change dist (f.toLp 2 (volume : Measure E))
        (LocalizedFourier.CM.Construction.localizedFourierMap hK.measurableSet hB.measurableSet (f.toLp 2 (volume : Measure E))) < ε
      rw [dist_eq_norm, LocalizedFourier.CM.Construction.localizedFourierMap_schwartz_support hK.measurableSet hB.measurableSet f hf]
      apply htail.trans_lt
      have hnorm' : Bounds.CM.Construction.sobolevNorm E ℂ 1 ⟨((f.toLp 2 (volume : Measure E)) : 𝓢'(E, ℂ)), hf'⟩ ≤ C := by
        simpa only [Lp.toTemperedDistribution_toLp_eq, schwartzSobolevNorm] using hnorm
      exact (mul_le_mul_of_nonneg_left hnorm' (inv_nonneg.mpr hR.le)).trans_lt hsmall
  exact htotal.closure.isCompact_of_isClosed isClosed_closure

end

section

/-! Hilbert-space realization of the genuine Sobolev inclusion. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def l2FourierMultiplierValue {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (f : Lp F 2 (volume : Measure E)) :
    Lp F 2 (volume : Measure E) := (Bounds.CM.Construction.fourierMultiplier_l2_bound hg hC f).choose

theorem l2FourierMultiplierValue_distribution {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (f : Lp F 2 (volume : Measure E)) :
    (l2FourierMultiplierValue hg hC f : 𝓢'(E, F)) =
      fourierMultiplierCLM F g (f : 𝓢'(E, F)) :=
  (Bounds.CM.Construction.fourierMultiplier_l2_bound hg hC f).choose_spec.1

theorem l2FourierMultiplierValue_norm_le {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (f : Lp F 2 (volume : Measure E)) :
    ‖l2FourierMultiplierValue hg hC f‖ ≤ C * ‖f‖ :=
  (Bounds.CM.Construction.fourierMultiplier_l2_bound hg hC f).choose_spec.2

/-- The bounded multiplier acts continuously on the actual L² Hilbert space. -/
def l2FourierMultiplier {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := l2FourierMultiplierValue hg hC
      map_add' := fun f h => by
        apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
          (F := F) (μ := (volume : Measure E)) (p := 2)))
        change (l2FourierMultiplierValue hg hC (f + h) : 𝓢'(E, F)) =
          ((l2FourierMultiplierValue hg hC f + l2FourierMultiplierValue hg hC h :
            Lp F 2 (volume : Measure E)) : 𝓢'(E, F))
        rw [l2FourierMultiplierValue_distribution]
        simp only [← Lp.toTemperedDistributionCLM_apply, map_add]
        congr 1 <;> exact (l2FourierMultiplierValue_distribution hg hC _).symm
      map_smul' := fun c f => by
        apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
          (F := F) (μ := (volume : Measure E)) (p := 2)))
        change (l2FourierMultiplierValue hg hC (c • f) : 𝓢'(E, F)) =
          ((c • l2FourierMultiplierValue hg hC f : Lp F 2 (volume : Measure E)) : 𝓢'(E, F))
        rw [l2FourierMultiplierValue_distribution]
        simp only [← Lp.toTemperedDistributionCLM_apply, map_smul]
        exact congrArg (c • ·) (l2FourierMultiplierValue_distribution hg hC f).symm }
    C (l2FourierMultiplierValue_norm_le hg hC)

theorem l2FourierMultiplier_distribution {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (f : Lp F 2 (volume : Measure E)) :
    (l2FourierMultiplier hg hC f : 𝓢'(E, F)) =
      fourierMultiplierCLM F g (f : 𝓢'(E, F)) :=
  l2FourierMultiplierValue_distribution hg hC f

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem negative_besselSymbol_bound {s : ℝ} (hs : 0 ≤ s) (x : E) :
    ‖(((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by simp)
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (by norm_num))

/-- The actual Sobolev inclusion, represented on its L² Bessel coordinates. -/
def sobolevL2Embedding {s : ℝ} (hs : 0 ≤ s) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  l2FourierMultiplier (g := fun x : E => (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ))
    (by fun_prop) (negative_besselSymbol_bound hs)

theorem sobolevL2Embedding_distribution {s : ℝ} (hs : 0 ≤ s)
    (f : Lp F 2 (volume : Measure E)) :
    (sobolevL2Embedding hs f : 𝓢'(E, F)) = besselPotential E F (-s) (f : 𝓢'(E, F)) :=
  l2FourierMultiplier_distribution (by fun_prop) (negative_besselSymbol_bound hs) f

theorem sobolevL2Embedding_norm_le {s : ℝ} (hs : 0 ≤ s)
    (f : Lp F 2 (volume : Measure E)) : ‖sobolevL2Embedding hs f‖ ≤ ‖f‖ := by
  change ‖l2FourierMultiplierValue
    (g := fun x : E => (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ))
    (by fun_prop) (negative_besselSymbol_bound hs) f‖ ≤ ‖f‖
  simpa only [one_mul] using l2FourierMultiplierValue_norm_le
    (g := fun x : E => (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ))
    (by fun_prop) (negative_besselSymbol_bound hs) f

theorem sobolevL2Embedding_injective {s : ℝ} (hs : 0 ≤ s) :
    Function.Injective (sobolevL2Embedding (E := E) (F := F) hs) := by
  intro f g h
  have heq := congrArg (fun u : Lp F 2 (volume : Measure E) =>
    besselPotential E F s (u : 𝓢'(E, F))) h
  simp only [sobolevL2Embedding_distribution, besselPotential_besselPotential_apply,
    neg_add_cancel, besselPotential_zero, ContinuousLinearMap.id_apply] at heq
  exact (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := F) (μ := (volume : Measure E)) (p := 2))) heq

end

/-! The completed Sobolev space of compactly supported functions and its compact inclusion. -/

open _root_.MeasureTheory TemperedDistribution Set _root_.Metric
open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Schwartz functions in the canonical L² Bessel coordinates of order s. -/
def schwartzSobolevCoordinate (s : ℝ) : 𝓢(E, ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (Bounds.CM.Construction.sobolevCoordinateEquiv E ℂ s).symm.toLinearMap.comp
    ((SchwartzMap.toTemperedDistributionCLM E ℂ (volume : Measure E)).toLinearMap.codRestrict
      (Bounds.CM.Construction.sobolevDistributionSubmodule E ℂ s) (fun f => f.memSobolev))

theorem schwartzSobolevCoordinate_norm (s : ℝ) (f : 𝓢(E, ℂ)) :
    ‖schwartzSobolevCoordinate s f‖ = schwartzSobolevNorm s f := rfl

theorem sobolevL2Embedding_schwartz {s : ℝ} (hs : 0 ≤ s) (f : 𝓢(E, ℂ)) :
    sobolevL2Embedding hs (schwartzSobolevCoordinate s f) = f.toLp 2 (volume : Measure E) := by
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure E)) (p := 2)))
  change ((sobolevL2Embedding hs (schwartzSobolevCoordinate s f)) : 𝓢'(E, ℂ)) =
    ((f.toLp 2 (volume : Measure E)) : 𝓢'(E, ℂ))
  rw [sobolevL2Embedding_distribution, Lp.toTemperedDistribution_toLp_eq]
  change besselPotential E ℂ (-s)
    (((Bounds.CM.Construction.sobolevCoordinateEquiv E ℂ s).symm
      ⟨(f : 𝓢'(E, ℂ)), f.memSobolev⟩) : 𝓢'(E, ℂ)) = _
  rw [Bounds.CM.Construction.sobolevCoordinateEquiv_symm_distribution, besselPotential_besselPotential_apply,
    add_neg_cancel, besselPotential_zero, ContinuousLinearMap.id_apply]

/-- The genuine linear subspace of Schwartz functions vanishing outside K. -/
def supportedSchwartzSubmodule (K : Set E) : Submodule ℂ 𝓢(E, ℂ) where
  carrier := {f | ∀ x ∉ K, f x = 0}
  zero_mem' := by
    change ∀ x ∉ K, (0 : 𝓢(E, ℂ)) x = 0
    intro x _
    rfl
  add_mem' hf hg := by intro x hx; simp only [add_apply, hf x hx, hg x hx, add_zero]
  smul_mem' c f hf := by intro x hx; simp only [smul_apply, hf x hx, smul_zero]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem supportedSchwartzSubmodule_mem_iff (K : Set E) (f : 𝓢(E, ℂ)) :
    f ∈ supportedSchwartzSubmodule K ↔ Function.support f ⊆ K := by
  constructor
  · intro h x hx
    by_contra hk
    exact hx (h x hk)
  · intro h x hx
    by_contra hf
    exact hx (h hf)

/-- Completion of the actual compactly supported smooth functions in their H¹ norm. -/
def supportedH1Coordinates (K : Set E) : Submodule ℂ (Lp ℂ 2 (volume : Measure E)) :=
  ((supportedSchwartzSubmodule K).map (schwartzSobolevCoordinate 1)).topologicalClosure

instance supportedH1Coordinates_complete (K : Set E) : CompleteSpace (supportedH1Coordinates K) :=
  ((supportedSchwartzSubmodule K).map (schwartzSobolevCoordinate 1)).isClosed_topologicalClosure.completeSpace_coe

/-- The completed space embeds into actual L² functions by inverse Bessel potential. -/
def supportedH1Embedding (K : Set E) :
    supportedH1Coordinates K →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (sobolevL2Embedding (E := E) (F := ℂ) (by norm_num : (0 : ℝ) ≤ 1)).comp
    (supportedH1Coordinates K).subtypeL

theorem supportedH1Embedding_injective (K : Set E) : Function.Injective (supportedH1Embedding K) :=
  (sobolevL2Embedding_injective (by norm_num : (0 : ℝ) ≤ 1)).comp Subtype.val_injective

/-- Completion still gives genuine distributional H¹ regularity. -/
theorem supportedH1Embedding_memSobolev (K : Set E) (u : supportedH1Coordinates K) :
    MemSobolev 1 2 ((supportedH1Embedding K u) : 𝓢'(E, ℂ)) := by
  change MemSobolev 1 2 ((sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u.val) : 𝓢'(E, ℂ))
  rw [sobolevL2Embedding_distribution, memSobolev_besselPotential_iff]
  norm_num only [neg_add_cancel]
  exact memSobolev_zero_iff.mpr ⟨u.val, rfl⟩

/-- The L² representative of a completed supported function vanishes almost everywhere outside K. -/
theorem supportedH1Embedding_support {K : Set E} (hK : MeasurableSet K)
    (u : supportedH1Coordinates K) :
    ∀ᵐ x ∂(volume : Measure E).restrict Kᶜ, supportedH1Embedding K u x = 0 := by
  let J := sobolevL2Embedding (E := E) (F := ℂ) (by norm_num : (0 : ℝ) ≤ 1)
  let P : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
    (LpLocalization.CM.Construction.lpSubtypeZeroExtension volume hK).toContinuousLinearMap.comp (LpLocalization.CM.Construction.lpSubtypeRestriction volume hK)
  have hclosed : IsClosed {v : Lp ℂ 2 (volume : Measure E) | P (J v) = J v} :=
    isClosed_eq (P.continuous.comp J.continuous) J.continuous
  have hdense : (((supportedSchwartzSubmodule K).map (schwartzSobolevCoordinate 1)) :
      Set (Lp ℂ 2 (volume : Measure E))) ⊆ {v | P (J v) = J v} := by
    rintro _ ⟨f, hf, rfl⟩
    change P (sobolevL2Embedding _ (schwartzSobolevCoordinate 1 f)) =
      sobolevL2Embedding _ (schwartzSobolevCoordinate 1 f)
    rw [sobolevL2Embedding_schwartz]
    apply Lp.ext
    filter_upwards [LpLocalization.CM.Construction.lpSubtype_localization_coeFn volume hK (f.toLp 2 (volume : Measure E)),
      f.coeFn_toLp 2 (volume : Measure E)] with x hx hfx
    change P (f.toLp 2 (volume : Measure E)) x = (f.toLp 2 (volume : Measure E)) x
    rw [show P (f.toLp 2 (volume : Measure E)) x = K.indicator
      (fun y => (f.toLp 2 (volume : Measure E)) y) x from hx]
    by_cases hxK : x ∈ K
    · exact Set.indicator_of_mem hxK _
    · rw [Set.indicator_of_notMem hxK, hfx, hf x hxK]
  have hfixed : P (J u.val) = J u.val := (closure_minimal hdense hclosed) u.property
  have hae := LpLocalization.CM.Construction.lpSubtype_localization_coeFn volume hK (J u.val)
  change P (J u.val) =ᵐ[volume] K.indicator (fun x => J u.val x) at hae
  rw [hfixed] at hae
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hK.compl] with x hx hk
  change J u.val x = 0
  exact hx.trans (Set.indicator_of_notMem hk _)

/-- Rellich compactness persists after completing the smooth compactly supported space. -/
theorem supportedH1Embedding_isCompact {K : Set E} (hK : IsCompact K) :
    IsCompactOperator (supportedH1Embedding K) := by
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (supportedH1Embedding K).toLinearMap (by norm_num : (0 : ℝ) < 1)).mpr
  let S := (fun f : 𝓢(E, ℂ) => f.toLp 2 (volume : Measure E)) ''
    {f | Function.support f ⊆ K ∧ schwartzSobolevNorm 1 f ≤ 2}
  refine ⟨closure S, schwartz_rellich_compact hK 2, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have huclosure : u.val ∈ closure
      (((supportedSchwartzSubmodule K).map (schwartzSobolevCoordinate 1)) : Set (Lp ℂ 2 volume)) :=
    u.property
  obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.mp huclosure (min 1 ε) (lt_min (by norm_num) hε)
  obtain ⟨f, hf, rfl⟩ := hw
  have hunorm : ‖u.val‖ ≤ 1 := by
    change ‖u‖ ≤ 1
    simpa only [Metric.mem_closedBall, dist_zero_right] using hu
  have hfnorm : schwartzSobolevNorm 1 f ≤ 2 := by
    rw [← schwartzSobolevCoordinate_norm]
    have hdist' : ‖schwartzSobolevCoordinate 1 f - u.val‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hdist.trans_le (min_le_left 1 ε)
    have hn := norm_le_norm_add_norm_sub u.val (schwartzSobolevCoordinate 1 f)
    rw [norm_sub_rev u.val] at hn
    linarith
  refine ⟨f.toLp 2 (volume : Measure E), ⟨f, ⟨?_, hfnorm⟩, rfl⟩, ?_⟩
  · exact (supportedSchwartzSubmodule_mem_iff K f).mp hf
  · rw [← sobolevL2Embedding_schwartz (by norm_num : (0 : ℝ) ≤ 1) f]
    change dist (sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u.val)
      (sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (schwartzSobolevCoordinate 1 f)) < ε
    rw [dist_eq_norm, ← map_sub]
    exact (sobolevL2Embedding_norm_le (by norm_num : (0 : ℝ) ≤ 1) _).trans_lt
      (by simpa only [dist_eq_norm] using hdist.trans_le (min_le_right 1 ε))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction
