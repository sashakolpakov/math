import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraWeylCoefficients
import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierUniformBound

/-! # Weyl Synthesis Add -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesisAdd.Construction

noncomputable section

section

/-! Compact support of nonarchimedean Weyl matrix coefficients, uniformly
controlled in the position and momentum coordinates. -/

open _root_.MeasureTheory _root_.Topology Filter
open scoped ComplexConjugate

theorem weylMatrixCoefficient_compactSupport_ultra
    {F : Type} [NormedField F] [LocallyCompactSpace F] [IsUltrametricDist F]
    [MeasurableSpace F] [BorelSpace F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ) (hn : ∃ a : F, ψ a ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [μ.IsAddHaarMeasure] (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    HasCompactSupport (WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val) := by
  let : ProperSpace F := TestSpaceAnalysis.Construction.localField_proper F hF
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  obtain ⟨hfl, hfs⟩ := UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp f.property
  obtain ⟨hhl, hhs⟩ := UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp h.property
  obtain ⟨Rf, hRf, hfb⟩ := hfs.isBounded.exists_pos_norm_le
  obtain ⟨Rh, hRh, hhb⟩ := hhs.isBounded.exists_pos_norm_le
  obtain ⟨εf, hεf, hft⟩ := FourierUltra.Construction.compact_locallyConstant_translation hfl hfs
  obtain ⟨εh, hεh, hht⟩ := FourierUltra.Construction.compact_locallyConstant_translation hhl hhs
  obtain ⟨a, ha⟩ := hn
  let ε := min εf εh
  have hε : 0 < ε := lt_min hεf hεh
  let Rq := ‖a‖ / ε
  have hRq : 0 ≤ Rq := div_nonneg (norm_nonneg _) hε.le
  let R := max (Rh + Rf) Rq
  have hR : 0 ≤ R := (add_pos hRh hRf).le.trans (le_max_left _ _)
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) R)
  intro v hv
  change WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val v ≠ 0 at hv
  have hp : ‖FourierCovariance.Construction.phasePosition v‖ ≤ Rh + Rf := by
    have hex : ∃ x, Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val x * conj (h.val x) ≠ 0 := by
      by_contra! hz
      apply hv
      exact integral_eq_zero_of_ae (Filter.Eventually.of_forall hz)
    obtain ⟨x, hx⟩ := hex
    have hfx : f.val (x - FourierCovariance.Construction.phasePosition v) ≠ 0 := by
      intro hz
      rw [FourierCovariance.Construction.heisenbergFunction_dot, hz, mul_zero, zero_mul] at hx
      exact hx rfl
    have hhx : h.val x ≠ 0 := by
      intro hz
      rw [hz, map_zero, mul_zero] at hx
      exact hx rfl
    calc
      ‖FourierCovariance.Construction.phasePosition v‖ = ‖x - (x - FourierCovariance.Construction.phasePosition v)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - FourierCovariance.Construction.phasePosition v‖ := norm_sub_le _ _
      _ ≤ Rh + Rf := add_le_add (hhb x (subset_tsupport _ hhx))
        (hfb (x - FourierCovariance.Construction.phasePosition v) (subset_tsupport _ hfx))
  have hq : ‖FourierCovariance.Construction.phaseMomentum v‖ ≤ Rq := by
    let k : Local.FunctionsMetaplectic.Construction.Position F d → ℂ := fun x => f.val (x - FourierCovariance.Construction.phasePosition v) * conj (h.val x)
    have hkt (x t : Local.FunctionsMetaplectic.Construction.Position F d) (ht : ‖t‖ < ε) : k (x + t) = k x := by
      have hxf : x + t - FourierCovariance.Construction.phasePosition v = (x - FourierCovariance.Construction.phasePosition v) + t := by abel
      dsimp only [k]
      rw [hxf, hft _ t (ht.trans_le (min_le_left _ _)), hht x t (ht.trans_le (min_le_right _ _))]
    have hnonzero : Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ k (-FourierCovariance.Construction.phaseMomentum v) ≠ 0 := by
      intro hz
      apply hv
      rw [UltraWeylCoefficients.Construction.weylMatrixCoefficient_fourier]
      change _ * Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ k (-FourierCovariance.Construction.phaseMomentum v) = 0
      rw [hz, mul_zero]
    simpa only [norm_neg] using FourierUniformBound.Construction.fourier_support_bound_of_translation ψ μ a ha ε hε k hkt _ hnonzero
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  cases i with
  | inl i => exact (norm_le_pi_norm (FourierCovariance.Construction.phasePosition v) i).trans (hp.trans (le_max_left _ _))
  | inr i => exact (norm_le_pi_norm (FourierCovariance.Construction.phaseMomentum v) i).trans (hq.trans (le_max_right _ _))

end

section

/-! Compact Weyl superpositions define actual Bruhat test functions. -/

open _root_.MeasureTheory _root_.Topology Filter

def weylSynthesis
    {F : Type} [NormedField F] [MeasurableSpace F] {d : ℕ}
    (ψ : AddChar F ℂ) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d))
    (a : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) : Local.FunctionsMetaplectic.Construction.Position F d → ℂ :=
  fun x => ∫ v, a v * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f x ∂ν

theorem weylSynthesis_mem_ultra
    {F : Type} [NormedField F] [LocallyCompactSpace F] [IsUltrametricDist F]
    [MeasurableSpace F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d))
    (a : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ) (ha : IsLocallyConstant a) (has : HasCompactSupport a)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : weylSynthesis ψ ν a f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := by
  let : ProperSpace F := TestSpaceAnalysis.Construction.localField_proper F hF
  obtain ⟨hfl, hfs⟩ := UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp f.property
  let k : Local.FunctionsMetaplectic.Construction.Position F d × Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ :=
    fun p => a p.2 * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ p.2 f.val p.1
  have hphase : Continuous (fun p : Local.FunctionsMetaplectic.Construction.Position F d × Local.FunctionsMetaplectic.Construction.PhaseSpace F d =>
      ∑ i, p.2 (Sum.inr i) * (p.1 i - p.2 (Sum.inl i) / 2)) := by fun_prop
  have hshift : Continuous (fun p : Local.FunctionsMetaplectic.Construction.Position F d × Local.FunctionsMetaplectic.Construction.PhaseSpace F d =>
      fun i => p.1 i - p.2 (Sum.inl i)) := by fun_prop
  have hk : IsLocallyConstant k := by
    unfold k Local.FunctionsMetaplectic.Construction.heisenbergFunction
    exact (ha.comp_continuous continuous_snd).mul
      (((LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hc).comp_continuous hphase).mul
        (hfl.comp_continuous hshift))
  apply Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
  · exact FourierUltra.Construction.locallyConstant_integral_of_uniform_compact_support ν k hk (tsupport a) has
      (fun x v hv => by simp only [k, image_eq_zero_of_notMem_tsupport hv, zero_mul])
  · let T := (fun p : Local.FunctionsMetaplectic.Construction.Position F d × Local.FunctionsMetaplectic.Construction.PhaseSpace F d => p.1 + FourierCovariance.Construction.phasePosition p.2) ''
      ((tsupport f.val) ×ˢ (tsupport a))
    have hT : IsCompact T := (hfs.prod has).image (by unfold FourierCovariance.Construction.phasePosition; fun_prop)
    apply HasCompactSupport.intro hT
    intro x hx
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun v => by
      change a v * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val x = 0
      by_cases hav : a v = 0
      · rw [hav, zero_mul]
      · have hxf : x - FourierCovariance.Construction.phasePosition v ∉ tsupport f.val := by
          intro hmem
          apply hx
          refine ⟨(x - FourierCovariance.Construction.phasePosition v, v), ⟨hmem, subset_tsupport _ hav⟩, ?_⟩
          exact sub_add_cancel x (FourierCovariance.Construction.phasePosition v)
        rw [FourierCovariance.Construction.heisenbergFunction_dot, image_eq_zero_of_notMem_tsupport hxf, mul_zero, mul_zero]

theorem weylSynthesis_integrand_integrable
    {F : Type} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] {d : ℕ}
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
    (a : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ) (ha : Continuous a) (has : HasCompactSupport a)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (x : Local.FunctionsMetaplectic.Construction.Position F d) :
    Integrable (fun v => a v * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val x) ν := by
  have hf := TestSpaceAnalysis.Construction.schwartzBruhat_continuous f.property
  have hcont : Continuous (fun v => a v * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val x) := by
    unfold Local.FunctionsMetaplectic.Construction.heisenbergFunction
    fun_prop
  exact hcont.integrable_of_hasCompactSupport has.mul_right

end

/-! Linearity in the compact Weyl synthesis amplitude. -/

open _root_.MeasureTheory

theorem weylSynthesis_add
    {F : Type} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] {d : ℕ}
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
    (a b : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ) (ha : Continuous a) (hb : Continuous b)
    (has : HasCompactSupport a) (hbs : HasCompactSupport b) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    weylSynthesis ψ ν (a + b) f.val = weylSynthesis ψ ν a f.val + weylSynthesis ψ ν b f.val := by
  funext x
  unfold weylSynthesis
  simp only [Pi.add_apply, add_mul]
  rw [integral_add (weylSynthesis_integrand_integrable ψ hc ν a ha has f x)
    (weylSynthesis_integrand_integrable ψ hc ν b hb hbs f x)]

theorem weylSynthesis_smul
    {F : Type} [NormedField F] [MeasurableSpace F] {d : ℕ}
    (ψ : AddChar F ℂ) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d))
    (a : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ) (z : ℂ) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    weylSynthesis ψ ν (z • a) f = z • weylSynthesis ψ ν a f := by
  funext x
  unfold weylSynthesis
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesisAdd.Construction
