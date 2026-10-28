import OAI.RepresentationTheory.Weil.UnitarySplitting.ModulationMeasure
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier

/-! # Fourier Ultra -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.FourierUltra.Construction

noncomputable section

section

/-! Injectivity of the Fourier integral from character-measure uniqueness. -/

open _root_.MeasureTheory BoundedContinuousFunction
open scoped ENNReal ComplexConjugate

variable {F : Type} [NormedField F] [CompleteSpace F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
variable (ψ : AddChar F ℂ) (hψ : Continuous (fun x : F => ψ x)) (hunit : ∀ t, ‖ψ t‖ = 1)
variable (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d))

omit [CompleteSpace F] in
include hψ hunit in
theorem modulation_mul_integrable (p : Local.FunctionsMetaplectic.Construction.Position F d)
    {f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ} (hf : Integrable f μ) :
    Integrable (fun x => UltraMultiplier.Construction.modulationCharacter ψ p x * f x) μ := by
  have hc : Continuous (UltraMultiplier.Construction.modulationCharacter ψ p) := (ModulationMeasure.Construction.boundedModulation ψ hψ hunit p).continuous
  apply hf.norm.mono (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    simp only [Pi.mul_apply, norm_mul, UltraMultiplier.Construction.modulationCharacter, hunit, one_mul, norm_norm, le_refl]

omit [NormedField F] [CompleteSpace F] [BorelSpace F] [SecondCountableTopology F] in
theorem nonnegative_density_finite {f : Local.FunctionsMetaplectic.Construction.Position F d → ℝ}
    (hf : Integrable f μ) (hpos : ∀ x, 0 ≤ f x) :
    IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) :=
  isFiniteMeasure_withDensity (ne_of_lt ((hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall hpos)).mp hf.hasFiniteIntegral))

omit [CompleteSpace F] in
theorem nonnegative_density_modulation {f : Local.FunctionsMetaplectic.Construction.Position F d → ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) (p : Local.FunctionsMetaplectic.Construction.Position F d) :
    (∫ x, UltraMultiplier.Construction.modulationCharacter ψ p x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫ x, UltraMultiplier.Construction.modulationCharacter ψ p x * (f x : ℂ) ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul
    hf.measurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hpos x)]
    change (f x : ℂ) * UltraMultiplier.Construction.modulationCharacter ψ p x = _
    exact mul_comm _ _

include hψ hunit in
theorem real_eq_zero_of_modulation_integrals [SigmaFinite μ]
    (hnontrivial : ∃ t, ψ t ≠ 1) {f : Local.FunctionsMetaplectic.Construction.Position F d → ℝ}
    (hf : Integrable f μ) (hc : Continuous f)
    (h : ∀ p : Local.FunctionsMetaplectic.Construction.Position F d, ∫ x, UltraMultiplier.Construction.modulationCharacter ψ p x * (f x : ℂ) ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  let u : Local.FunctionsMetaplectic.Construction.Position F d → ℝ := fun x => |f x| + f x
  let v : Local.FunctionsMetaplectic.Construction.Position F d → ℝ := fun x => |f x| - f x
  have hu : ∀ x, 0 ≤ u x := by
    intro x
    dsimp [u]
    have hh := neg_abs_le (f x)
    linarith
  have hv : ∀ x, 0 ≤ v x := fun x => sub_nonneg.mpr (le_abs_self (f x))
  have huc : Continuous u := hc.abs.add hc
  have hvc : Continuous v := hc.abs.sub hc
  let : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (u x))) :=
    nonnegative_density_finite μ (hf.abs.add hf) hu
  let : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (v x))) :=
    nonnegative_density_finite μ (hf.abs.sub hf) hv
  have hmeasure : μ.withDensity (fun x => ENNReal.ofReal (u x)) =
      μ.withDensity (fun x => ENNReal.ofReal (v x)) := by
    apply ModulationMeasure.Construction.measures_eq_of_modulation_integrals ψ hψ hunit hnontrivial
    intro p
    rw [nonnegative_density_modulation ψ μ huc hu p,
      nonnegative_density_modulation ψ μ hvc hv p]
    simp only [u, v, Complex.ofReal_add, Complex.ofReal_sub, mul_add, mul_sub]
    have habs : Integrable (fun x => UltraMultiplier.Construction.modulationCharacter ψ p x * ((|f x| : ℝ) : ℂ)) μ :=
      modulation_mul_integrable ψ hψ hunit μ p (Complex.ofRealCLM.integrable_comp hf.abs)
    have hfi : Integrable (fun x => UltraMultiplier.Construction.modulationCharacter ψ p x * (f x : ℂ)) μ :=
      modulation_mul_integrable ψ hψ hunit μ p (Complex.ofRealCLM.integrable_comp hf)
    rw [integral_add habs hfi, integral_sub habs hfi, h]
    simp
  have hae := (withDensity_eq_iff_of_sigmaFinite huc.measurable.ennreal_ofReal.aemeasurable
    hvc.measurable.ennreal_ofReal.aemeasurable).mp hmeasure
  filter_upwards [hae] with x hx
  have hh := (ENNReal.ofReal_eq_ofReal_iff (hu x) (hv x)).mp hx
  dsimp [u, v] at hh
  change f x = 0
  linarith

omit [CompleteSpace F] [BorelSpace F] [SecondCountableTopology F] in
include hψ hunit in
theorem modulation_conjugate_integral (p : Local.FunctionsMetaplectic.Construction.Position F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    (∫ x, UltraMultiplier.Construction.modulationCharacter ψ p x * conj (f x) ∂μ) =
      conj (∫ x, UltraMultiplier.Construction.modulationCharacter ψ (-p) x * f x ∂μ) := by
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    have hn : UltraMultiplier.Construction.modulationCharacter ψ (-p) x = conj (UltraMultiplier.Construction.modulationCharacter ψ p x) :=
      congrArg (fun g : Local.FunctionsMetaplectic.Construction.Position F d →ᵇ ℂ => g x) (ModulationMeasure.Construction.boundedModulation_neg ψ hψ hunit p)
    simp only [map_mul, hn, starRingEnd_self_apply]

include hψ hunit in
theorem realPart_eq_zero_of_modulation_integrals [SigmaFinite μ]
    (hnontrivial : ∃ t, ψ t ≠ 1) {f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ}
    (hf : Integrable f μ) (hc : Continuous f)
    (h : ∀ p : Local.FunctionsMetaplectic.Construction.Position F d, ∫ x, UltraMultiplier.Construction.modulationCharacter ψ p x * f x ∂μ = 0) :
    (fun x => (f x).re) =ᵐ[μ] 0 := by
  apply real_eq_zero_of_modulation_integrals ψ hψ hunit μ hnontrivial
    (f := fun x => (f x).re) hf.re (Complex.continuous_re.comp hc)
  intro p
  have heq : (fun x => UltraMultiplier.Construction.modulationCharacter ψ p x * ((f x).re : ℂ)) =
      (fun x => (UltraMultiplier.Construction.modulationCharacter ψ p x * f x +
        UltraMultiplier.Construction.modulationCharacter ψ p x * conj (f x)) / 2) := by
    funext x
    rw [Complex.re_eq_add_conj]
    ring
  rw [heq, integral_div, integral_add]
  · rw [h, modulation_conjugate_integral ψ hψ hunit μ, h]
    simp
  · exact modulation_mul_integrable ψ hψ hunit μ p hf
  · apply modulation_mul_integrable ψ hψ hunit μ p
    apply hf.norm.mono (Complex.continuous_conj.comp hc).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by simp

include hψ hunit in
theorem complex_eq_zero_of_modulation_integrals [SigmaFinite μ]
    (hnontrivial : ∃ t, ψ t ≠ 1) {f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ}
    (hf : Integrable f μ) (hc : Continuous f)
    (h : ∀ p : Local.FunctionsMetaplectic.Construction.Position F d, ∫ x, UltraMultiplier.Construction.modulationCharacter ψ p x * f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  have hre := realPart_eq_zero_of_modulation_integrals ψ hψ hunit μ hnontrivial hf hc h
  have him := realPart_eq_zero_of_modulation_integrals ψ hψ hunit μ hnontrivial
    (hf.mul_const (-Complex.I)) (hc.mul continuous_const) (fun p => by
      simp only [← mul_assoc, integral_mul_const, h, zero_mul])
  filter_upwards [hre, him] with x hx hy
  apply Complex.ext
  · exact hx
  · simpa using hy

include hψ hunit in
theorem fourierIntegral_eq_zero_implies_ae_zero [SigmaFinite μ]
    (hnontrivial : ∃ t, ψ t ≠ 1) {f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ}
    (hf : Integrable f μ) (hc : Continuous f)
    (h : Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f = 0) : f =ᵐ[μ] 0 := by
  apply complex_eq_zero_of_modulation_integrals ψ hψ hunit μ hnontrivial hf hc
  intro p
  have hh := congrFun h (-p)
  change (∫ x, f x * ψ (-Local.FunctionsMetaplectic.Construction.dot (-p) x) ∂μ) = 0 at hh
  have hn (x : Local.FunctionsMetaplectic.Construction.Position F d) : -Local.FunctionsMetaplectic.Construction.dot (-p) x = Local.FunctionsMetaplectic.Construction.dot p x := by simp [Local.FunctionsMetaplectic.Construction.dot]
  simpa only [hn, UltraMultiplier.Construction.modulationCharacter, mul_comm] using hh

end

section

/-! Compact locally constant Fourier analysis for UnitarySplitting. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem character_finset_sum {k ι : Type*} [AddCommMonoid k]
    (ψ : AddChar k ℂ) (s : Finset ι) (a : ι → k) :
    ψ (∑ i ∈ s, a i) = ∏ i ∈ s, ψ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi, ψ.map_add_eq_mul, ih]

theorem compact_locallyConstant_translation
    {E : Type*} [NormedAddCommGroup E] {f : E → ℂ}
    (hf : IsLocallyConstant f) (hs : HasCompactSupport f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x t : E, ‖t‖ < ε → f (x + t) = f x := by
  let : UniformSpace ℂ := ⊥
  have hu : UniformContinuous f := hs.uniformContinuous_of_continuous hf.continuous
  have h : {p : E × E | f p.1 = f p.2} ∈ uniformity E :=
    hu (DiscreteUniformity.relId_mem_uniformity ℂ)
  obtain ⟨ε, hε, heq⟩ := Metric.mem_uniformity_dist.mp h
  refine ⟨ε, hε, fun x t ht => heq (a := x + t) (b := x) ?_⟩
  simpa [dist_eq_norm] using ht

theorem fourierIntegral_translate
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ) (t x : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun y => f (y + t)) x = ψ (Local.FunctionsMetaplectic.Construction.dot x t) * Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x := by
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  rw [← integral_const_mul]
  have h := integral_add_right_eq_self (μ := μ)
    (fun y => ψ (Local.FunctionsMetaplectic.Construction.dot x t) * (f y * ψ (-Local.FunctionsMetaplectic.Construction.dot x y))) t
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    have hp : Local.FunctionsMetaplectic.Construction.dot x (y + t) = Local.FunctionsMetaplectic.Construction.dot x y + Local.FunctionsMetaplectic.Construction.dot x t := by
      simp [Local.FunctionsMetaplectic.Construction.dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hp, neg_add, ψ.map_add_eq_mul]
    have hc : ψ (Local.FunctionsMetaplectic.Construction.dot x t) * ψ (-Local.FunctionsMetaplectic.Construction.dot x t) = 1 := by
      rw [← ψ.map_add_eq_mul]
      simp
    linear_combination -(f (y + t) * ψ (-Local.FunctionsMetaplectic.Construction.dot x y)) * hc

theorem fourierIntegral_vanishes_of_translation
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ) (t x : Local.FunctionsMetaplectic.Construction.Position k n)
    (ht : ∀ y, f (y + t) = f y) (hx : ψ (Local.FunctionsMetaplectic.Construction.dot x t) ≠ 1) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x = 0 := by
  have h := fourierIntegral_translate ψ μ f t x
  have heq : (fun y => f (y + t)) = f := funext ht
  rw [heq] at h
  by_contra hn
  apply hx
  apply mul_right_cancel₀ hn
  simpa using h.symm

theorem fourierIntegral_compactSupport_of_locallyConstant
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hNontrivial : ∃ a : k, ψ a ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    {f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : IsLocallyConstant f) (hs : HasCompactSupport f) :
    HasCompactSupport (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) := by
  let : ProperSpace k := TestSpaceAnalysis.Construction.localField_proper k hNondiscrete
  let : SecondCountableTopology k := TestSpaceAnalysis.Construction.localField_secondCountable k hNondiscrete
  obtain ⟨ε, hε, heq⟩ := compact_locallyConstant_translation hf hs
  obtain ⟨a, ha⟩ := hNontrivial
  have hR : 0 ≤ ‖a‖ / ε := div_nonneg (norm_nonneg _) hε.le
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Local.FunctionsMetaplectic.Construction.Position k n) (‖a‖ / ε))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  by_contra! hi
  have hxi : x i ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt hR hi)
  let t : Local.FunctionsMetaplectic.Construction.Position k n := Pi.single i (a / x i)
  have ht : ‖t‖ < ε := by
    rw [show ‖t‖ = ‖a / x i‖ from Pi.norm_single _, norm_div]
    apply (div_lt_iff₀ (norm_pos_iff.mpr hxi)).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hi
  have hdot : Local.FunctionsMetaplectic.Construction.dot x t = a := by
    simp only [Local.FunctionsMetaplectic.Construction.dot, t, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    field_simp
  have hzero := fourierIntegral_vanishes_of_translation ψ μ f t x
    (fun y => heq y t ht) (by rwa [hdot])
  exact hx hzero

theorem fourierIntegral_locallyConstant
    {k : Type} [NormedField k] [MeasurableSpace k] {n : ℕ}
    (ψ : AddChar k ℂ) (hψ : IsLocallyConstant (fun t => ψ t))
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n))
    {f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ} (hs : HasCompactSupport f) :
    IsLocallyConstant (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) := by
  obtain ⟨R, hR, hbound⟩ := hs.isBounded.exists_pos_norm_le
  obtain ⟨ε, hε, hker⟩ := Metric.eventually_nhds_iff.mp (hψ.eventually_eq 0)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨ε / R, div_pos hε hR, fun y hy => ?_⟩
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only
    by_cases hz : f z = 0
    · simp [hz]
    have hzR : ‖z‖ ≤ R := hbound z (subset_tsupport f hz)
    have hsmall : ‖y - x‖ * R < ε :=
      (lt_div_iff₀ hR).mp (by simpa [dist_eq_norm] using hy)
    have hchar : ψ (-Local.FunctionsMetaplectic.Construction.dot (y - x) z) = 1 := by
      rw [Local.FunctionsMetaplectic.Construction.dot, ← Finset.sum_neg_distrib, character_finset_sum]
      apply Finset.prod_eq_one
      intro i _
      have hnorm : ‖-((y - x) i * z i)‖ < ε := by
        rw [norm_neg, norm_mul]
        calc
          _ ≤ ‖y - x‖ * R := mul_le_mul
            (norm_le_pi_norm (y - x) i) ((norm_le_pi_norm z i).trans hzR)
            (norm_nonneg _) (norm_nonneg _)
          _ < ε := hsmall
      simpa only [ψ.map_zero_eq_one] using hker
        (show dist (-((y - x) i * z i)) 0 < ε by simpa using hnorm)
    have hsplit : -Local.FunctionsMetaplectic.Construction.dot y z = -Local.FunctionsMetaplectic.Construction.dot x z + -Local.FunctionsMetaplectic.Construction.dot (y - x) z := by
      simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hsplit, ψ.map_add_eq_mul, hchar, mul_one]

theorem ultra_fourier_mem
    {F : Type} [NormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [IsUltrametricDist F]
    (hF : ¬ DiscreteTopology F) {d : ℕ}
    (ψ : AddChar F ℂ) (hc : Continuous (fun t : F => ψ t))
    (hnontrivial : ∃ t, ψ t ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [μ.IsAddHaarMeasure] (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := by
  obtain ⟨hf, hs⟩ := UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp f.property
  exact Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
    (fourierIntegral_locallyConstant ψ (LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hc) μ hs)
    (fourierIntegral_compactSupport_of_locallyConstant hF ψ hnontrivial μ hf hs)

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [IsUltrametricDist F]
variable {d : ℕ} (hF : ¬ DiscreteTopology F)
variable (ψ : AddChar F ℂ) (hc : Continuous (fun t : F => ψ t))
variable (hunit : ∀ t, ‖ψ t‖ = 1) (hnontrivial : ∃ t, ψ t ≠ 1)
variable (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [μ.IsAddHaarMeasure]

omit [CompleteSpace F] [LocallyCompactSpace F] [IsUltrametricDist F] in
include hc hunit in
theorem fourier_kernel_integrable (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (x : Local.FunctionsMetaplectic.Construction.Position F d) :
    Integrable (fun y => f.val y * ψ (-Local.FunctionsMetaplectic.Construction.dot x y)) μ := by
  have hh := modulation_mul_integrable ψ hc hunit μ (-x)
    (TestSpaceAnalysis.Construction.schwartzBruhat_integrable μ f)
  have heq : (fun y => UltraMultiplier.Construction.modulationCharacter ψ (-x) y * f.val y) =
      (fun y => f.val y * ψ (-Local.FunctionsMetaplectic.Construction.dot x y)) := by
    funext y
    have hn : Local.FunctionsMetaplectic.Construction.dot (-x) y = -Local.FunctionsMetaplectic.Construction.dot x y := by simp [Local.FunctionsMetaplectic.Construction.dot]
    rw [UltraMultiplier.Construction.modulationCharacter, hn, mul_comm]
  rw [heq] at hh
  exact hh

def ultraFourierLinearMap : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d where
  toFun f := ⟨Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val, ultra_fourier_mem hF ψ hc hnontrivial μ f⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact Local.FunctionsMetaplectic.Construction.fourierIntegral_add ψ μ f.val g.val x
      (fourier_kernel_integrable ψ hc hunit μ f x) (fourier_kernel_integrable ψ hc hunit μ g x)
  map_smul' z f := Subtype.ext (Local.FunctionsMetaplectic.Construction.fourierIntegral_smul ψ μ z f.val)

theorem ultraFourierLinearMap_injective :
    Function.Injective (ultraFourierLinearMap hF ψ hc hunit hnontrivial μ) := by
  intro f g hfg
  apply sub_eq_zero.mp
  have hzero : ultraFourierLinearMap hF ψ hc hunit hnontrivial μ (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hh : Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (f - g).val = 0 := congrArg Subtype.val hzero
  have hae := fourierIntegral_eq_zero_implies_ae_zero ψ hc hunit μ hnontrivial
    (TestSpaceAnalysis.Construction.schwartzBruhat_integrable μ (f - g)) (TestSpaceAnalysis.Construction.schwartzBruhat_continuous (f - g).property) hh
  exact Subtype.ext (Measure.eq_of_ae_eq hae
    (TestSpaceAnalysis.Construction.schwartzBruhat_continuous (f - g).property) continuous_const)

end

/-! Parameter integrals of locally constant functions with a common
compact support in the integration variable are locally constant. -/

open _root_.MeasureTheory _root_.Topology Filter

theorem locallyConstant_integral_of_uniform_compact_support
    {V X : Type} [NormedAddCommGroup V] [IsUltrametricDist V] [ProperSpace V]
    [NormedAddCommGroup X] [MeasurableSpace X]
    (μ : Measure X) (k : V × X → ℂ) (hk : IsLocallyConstant k)
    (K : Set X) (hK : IsCompact K) (hsupport : ∀ v x, x ∉ K → k (v, x) = 0) :
    IsLocallyConstant (fun v : V => ∫ x, k (v, x) ∂μ) := by
  classical
  rw [IsLocallyConstant.iff_eventually_eq]
  intro v
  let U := Metric.closedBall v 1
  have hU : IsClopen U := IsUltrametricDist.isClopen_closedBall v one_ne_zero
  let j : V × X → ℂ := fun p => (LocallyConstant.charFn ℂ hU p.1) * k p
  have hj : IsLocallyConstant j :=
    ((LocallyConstant.charFn ℂ hU).isLocallyConstant.comp_continuous continuous_fst).mul hk
  have hjs : HasCompactSupport j := by
    apply HasCompactSupport.intro ((isCompact_closedBall v 1).prod hK)
    intro p hp
    by_cases hv : p.1 ∈ U
    · have hx : p.2 ∉ K := fun hx => hp ⟨hv, hx⟩
      simp only [j, hsupport p.1 p.2 hx, mul_zero]
    · have hz : LocallyConstant.charFn ℂ hU p.1 = 0 :=
        (LocallyConstant.charFn_eq_zero ℂ p.1 hU).mpr hv
      simp only [j, hz, zero_mul]
  obtain ⟨ε, hε, htrans⟩ := compact_locallyConstant_translation hj hjs
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨min ε 1, lt_min hε zero_lt_one, fun w hw => ?_⟩
  have hwU : w ∈ U := (Metric.mem_closedBall).mpr (le_of_lt (hw.trans_le (min_le_right _ _)))
  have hvU : v ∈ U := Metric.mem_closedBall_self zero_le_one
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have hshift : ‖(w - v, (0 : X))‖ < ε := by
      change max ‖w - v‖ ‖(0 : X)‖ < ε
      rw [norm_zero, max_eq_left (norm_nonneg (w - v)), ← dist_eq_norm]
      exact hw.trans_le (min_le_left _ _)
    have hh := htrans (v, x) (w - v, 0) hshift
    have hwone := (LocallyConstant.charFn_eq_one ℂ w hU).mpr hwU
    have hvone := (LocallyConstant.charFn_eq_one ℂ v hU).mpr hvU
    have hp : (v, x) + (w - v, 0) = (w, x) := by
      apply Prod.ext
      · change v + (w - v) = w
        abel
      · exact add_zero x
    rw [hp] at hh
    simpa only [j, hwone, hvone, one_mul] using hh

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.FourierUltra.Construction
