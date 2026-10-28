import OAI.RepresentationTheory.Weil.Local.CompactQuadraticPhase
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanNormalization

/-! # Gaussian Nonarchimedean -/

namespace OAI.RepresentationTheory.Weil.Local.GaussianNonarchimedean.Construction

noncomputable section

section

/-! The eighth-root phase of the actual nonarchimedean local Gaussian. -/

open _root_.MeasureTheory Filter
open scoped Classical _root_.Topology

theorem nonarchimedean_gaussianIndex_eighth
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : k) (ha : a ≠ 0) : FunctionsMetaplectic.Construction.gaussianIndex k ψ a ^ 8 = 1 := by
  obtain ⟨U, V, hU, hV, hVU, hphase, hdual, hradial, hG⟩ :=
    GaussianCompact.Construction.exists_compactGaussian_domain hNondiscrete ψ hu hc hn a ha
  have hlim := GaussianCompact.Construction.regularizedGaussian_tendsto_compact_of_domain hNondiscrete ψ hu hc a
    U V hU hV hVU hphase hdual hradial
  have hGval : FunctionsMetaplectic.Construction.gaussianIntegral k ψ a =
      ∫ y in (U : Set k), ψ (a * y ^ 2 / 2) ∂(Measure.addHaar : Measure k) := hlim.limUnder_eq
  change FunctionsMetaplectic.Construction.phase (FunctionsMetaplectic.Construction.gaussianIntegral k ψ a) ^ 8 = 1
  rw [hGval]
  let q := CompactQuadraticPhase.Construction.localQuadraticCharacter ψ hu a
  have hqc : Continuous (fun x => q x) := hc.comp (by fun_prop)
  apply q.compact_integral_phase_eighth Measure.addHaar hqc U V hU hphase _ hG
  intro x hx y hy
  change ψ (a * x * y) = 1
  rw [show a * x * y = a * y * x by ring]
  exact (hdual y).mp hy x hx

theorem nonarchimedean_gaussian_normalization
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : k) (ha : a ≠ 0) :
    Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) ∧
      FunctionsMetaplectic.Construction.gaussianIntegral k ψ a ≠ 0 ∧ FunctionsMetaplectic.Construction.gaussianIndex k ψ a ^ 8 = 1 := by
  obtain ⟨hlim, hG⟩ := GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hNondiscrete ψ hu hc hn a ha
  exact ⟨hlim, hG, nonarchimedean_gaussianIndex_eighth hNondiscrete ψ hu hc hn a ha⟩

/-- All four analytic clauses, with the reference-set normalization and actual Gaussian limit. -/
theorem nonarchimedean_analytic_normalization
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) (n : ℕ) :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ ∧
    (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure ∧
    (∀ a : k, a ≠ 0 →
      Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) ∧
      FunctionsMetaplectic.Construction.gaussianIntegral k ψ a ≠ 0 ∧ FunctionsMetaplectic.Construction.gaussianIndex k ψ a ^ 8 = 1) ∧
    (∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n),
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
        (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val) x = f.val (-x)) := by
  exact ⟨(NonarchimedeanHaar.Construction.nonarchimedean_reference_scale hNondiscrete ψ hu hc hn).1,
    NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hNondiscrete ψ hu hc hn,
    nonarchimedean_gaussian_normalization hNondiscrete ψ hu hc hn,
    NonarchimedeanNormalization.Construction.nonarchimedean_fourier_inversion_selfDual hNondiscrete n ψ hu hc hn⟩

end

section

/-! The scalar normalization needed for the exact Weyl operator. -/

open _root_.MeasureTheory Filter
open scoped Classical ComplexConjugate _root_.Topology

theorem unitary_character_neg {k : Type*} [AddGroup k]
    (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (x : k) : ψ (-x) = conj (ψ x) := by
  rw [ψ.map_neg_eq_inv, Complex.inv_eq_conj (hu x)]

theorem regularizedGaussian_neg
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (a : k) (ε : ℝ) :
    FunctionsMetaplectic.Construction.regularizedGaussian k ψ (-a) ε = conj (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a ε) := by
  unfold FunctionsMetaplectic.Construction.regularizedGaussian
  rw [← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [map_mul, Complex.conj_ofReal, ← unitary_character_neg ψ hu]
    congr 2
    ring

theorem nonarchimedean_gaussianIntegral_neg
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : k) (ha : a ≠ 0) : FunctionsMetaplectic.Construction.gaussianIntegral k ψ (-a) = conj (FunctionsMetaplectic.Construction.gaussianIntegral k ψ a) := by
  have h := (Complex.continuous_conj.tendsto _).comp
    (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hNondiscrete ψ hu hc hn a ha).1
  have hneg : Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ (-a)) (𝓝[>] (0 : ℝ))
      (𝓝 (conj (FunctionsMetaplectic.Construction.gaussianIntegral k ψ a))) := by
    simpa only [Function.comp_def, ← regularizedGaussian_neg ψ hu] using h
  exact hneg.limUnder_eq

theorem scalarFourier_compactQuadratic_full
    {k : Type} [NormedField k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (ψ : AddChar k ℂ) (a : k) (ha : a ≠ 0)
    (U V : OpenAddSubgroup k) (hVU : V ≤ U)
    (hphase : ∀ t ∈ V, ψ (a * t ^ 2 / 2) = 1)
    (hdual : ∀ y, y ∈ U ↔ a * y ∈ QuadraticFourier.Construction.scalarAnnihilator ψ V.toAddSubgroup) (x : k) :
    FourierTensor.Construction.scalarFourierIntegral ψ Measure.addHaar (QuadraticFourier.Construction.compactQuadraticFunction ψ U a) x =
      (∫ y in (U : Set k), ψ (a * y ^ 2 / 2) ∂(Measure.addHaar : Measure k)) *
        QuadraticFourier.Construction.compactQuadraticFunction ψ U (-a) (x / a) := by
  have hax : a * (x / a) = x := by field_simp
  by_cases hx : x / a ∈ U
  · have h := QuadraticFourier.Construction.scalarFourier_compactQuadratic ψ Measure.addHaar U a (x / a) hx
    rw [hax] at h
    rw [h, QuadraticFourier.Construction.compactQuadraticFunction, Set.indicator_of_mem hx, mul_comm]
    congr 2
    ring
  · rw [show QuadraticFourier.Construction.compactQuadraticFunction ψ U (-a) (x / a) = 0 from
      Set.indicator_of_notMem hx _, mul_zero]
    have hnot : ¬ ∀ t ∈ V, ψ (x * t) = 1 := by
      intro hh
      apply hx
      apply (hdual (x / a)).mpr
      intro t ht
      rw [hax]
      exact hh t ht
    push Not at hnot
    obtain ⟨t, ht, htψ⟩ := hnot
    apply QuadraticFourier.Construction.scalarFourier_vanishes_of_translation ψ Measure.addHaar _ t x _ htψ
    apply QuadraticFourier.Construction.compactQuadratic_translation ψ U a t (hVU ht) (hphase t ht)
    intro y hy
    exact (hdual y).mp hy t ht

theorem compactGaussian_one_norm_sq
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (U V : OpenAddSubgroup k) (hU : IsCompact (U : Set k)) (hVU : V ≤ U)
    (hphase : ∀ t ∈ V, ψ (1 * t ^ 2 / 2) = 1)
    (hdual : ∀ y, y ∈ U ↔ 1 * y ∈ QuadraticFourier.Construction.scalarAnnihilator ψ V.toAddSubgroup) :
    ‖∫ y in (U : Set k), ψ (y ^ 2 / 2) ∂(Measure.addHaar : Measure k)‖ ^ 2 =
      FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let G := ∫ y in (U : Set k), ψ (y ^ 2 / 2) ∂(Measure.addHaar : Measure k)
  let q := QuadraticFourier.Construction.compactQuadraticFunction ψ U 1
  have hF : FourierTensor.Construction.scalarFourierIntegral ψ Measure.addHaar q = fun x => G * conj (q x) := by
    funext x
    rw [scalarFourier_compactQuadratic_full ψ 1 one_ne_zero U V hVU hphase hdual]
    simp only [one_mul, div_one]
    congr 1
    by_cases hx : x ∈ U
    · simp only [q, QuadraticFourier.Construction.compactQuadraticFunction, Set.indicator_of_mem hx, one_mul]
      rw [← unitary_character_neg ψ hu]
      congr 1
      ring
    · simp [q, QuadraticFourier.Construction.compactQuadraticFunction, hx]
  have hFF := FourierTensor.Construction.scalarFourier_square_reference hNondiscrete ψ hu hc hn
    (GaussianCompact.Construction.compactQuadratic_locallyConstant ψ hu hc U 1) (GaussianCompact.Construction.compactQuadratic_compactSupport ψ U hU 1) 0
  change FourierTensor.Construction.scalarFourierIntegral ψ Measure.addHaar (FourierTensor.Construction.scalarFourierIntegral ψ Measure.addHaar q) 0 =
    (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) * q (-0) at hFF
  rw [hF, FourierTensor.Construction.scalarFourierIntegral] at hFF
  simp only [zero_mul, neg_zero, ψ.map_zero_eq_one, mul_one] at hFF
  have hq0 : q 0 = 1 := by simp [q, QuadraticFourier.Construction.compactQuadraticFunction]
  have hqi : (∫ x, q x ∂(Measure.addHaar : Measure k)) = G := by
    simp only [q, QuadraticFourier.Construction.compactQuadraticFunction, one_mul]
    exact integral_indicator U.isOpen.measurableSet
  rw [integral_const_mul, integral_conj, hqi, hq0, mul_one,
    Complex.mul_conj, Complex.normSq_eq_norm_sq] at hFF
  exact_mod_cast hFF

theorem nonarchimedean_gaussianIntegral_one_norm
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) :
    ‖FunctionsMetaplectic.Construction.gaussianIntegral k ψ 1‖ = Real.sqrt (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ) := by
  obtain ⟨U, V, hU, hV, hVU, hphase, hdual, hradial, _⟩ :=
    GaussianCompact.Construction.exists_compactGaussian_domain hNondiscrete ψ hu hc hn 1 one_ne_zero
  have hlim := GaussianCompact.Construction.regularizedGaussian_tendsto_compact_of_domain hNondiscrete ψ hu hc 1
    U V hU hV hVU hphase hdual hradial
  have heq : FunctionsMetaplectic.Construction.gaussianIntegral k ψ 1 =
      ∫ y in (U : Set k), ψ (y ^ 2 / 2) ∂(Measure.addHaar : Measure k) := by
    simpa only [FunctionsMetaplectic.Construction.gaussianIntegral, one_mul] using! hlim.limUnder_eq
  rw [heq, ← compactGaussian_one_norm_sq hNondiscrete ψ hu hc hn U V hU hVU hphase hdual,
    Real.sqrt_sq (norm_nonneg _)]

end

/-! Arbitrarily large compact cutoffs with the exact self-dual Gaussian scalar. -/

open _root_.MeasureTheory
open scoped Classical ComplexConjugate

theorem phase_conj (z : ℂ) : FunctionsMetaplectic.Construction.phase (conj z) = conj (FunctionsMetaplectic.Construction.phase z) := by
  simp only [FunctionsMetaplectic.Construction.phase, map_div₀, Complex.conj_ofReal, Complex.norm_conj]

theorem nonarchimedean_gaussianIndex_neg
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : k) (ha : a ≠ 0) : FunctionsMetaplectic.Construction.gaussianIndex k ψ (-a) = (FunctionsMetaplectic.Construction.gaussianIndex k ψ a)⁻¹ := by
  rw [FunctionsMetaplectic.Construction.gaussianIndex, nonarchimedean_gaussianIntegral_neg hNondiscrete ψ hu hc hn a ha, phase_conj]
  exact (Complex.inv_eq_conj (FunctionsMetaplectic.Construction.gaussianIndex_norm k ψ a
    (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hNondiscrete ψ hu hc hn a ha).2)).symm

theorem integral_selfDualMeasure
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k ℂ) (f : k → ℂ) :
    (∫ x, f x ∂ FunctionsMetaplectic.Construction.selfDualMeasure k ψ) =
      ((Real.sqrt (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ))⁻¹ : ℝ) •
        ∫ x, f x ∂(Measure.addHaar : Measure k) := by
  rw [FunctionsMetaplectic.Construction.selfDualMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

theorem exists_gaussian_one_cutoff
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (K : Set k) (hK : IsCompact K) :
    ∃ W : OpenAddSubgroup k, IsCompact (W : Set k) ∧ K ⊆ W ∧
      (∫ x in (W : Set k), ψ (x ^ 2 / 2) ∂ FunctionsMetaplectic.Construction.selfDualMeasure k ψ) = FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  obtain ⟨U, V, hU, hV, hVU, hphase, hdual, hradial, _⟩ :=
    GaussianCompact.Construction.exists_compactGaussian_domain hNondiscrete ψ hu hc hn 1 one_ne_zero
  obtain ⟨R, hR, hbound⟩ := (hK.union hU).isBounded.exists_pos_norm_le
  let W := IsUltrametricDist.closedBall_openAddSubgroup k hR
  have hKW : K ⊆ W := fun x hx => by
    change x ∈ Metric.closedBall 0 R
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound x (Or.inl hx)
  have hUW : U ≤ W := fun x hx => by
    change x ∈ Metric.closedBall 0 R
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound x (Or.inr hx)
  have hW : IsCompact (W : Set k) := isCompact_closedBall 0 R
  have hlim := GaussianCompact.Construction.regularizedGaussian_tendsto_compact_of_domain hNondiscrete ψ hu hc 1
    U V hU hV hVU hphase hdual hradial
  have hGval : FunctionsMetaplectic.Construction.gaussianIntegral k ψ 1 =
      ∫ x in (W : Set k), ψ (x ^ 2 / 2) ∂(Measure.addHaar : Measure k) := by
    have h := GaussianCompact.Construction.compactGaussian_stabilizes_of_annihilator ψ hc Measure.addHaar 1 U V W hV hW
      hVU hUW hphase hdual
    simpa only [FunctionsMetaplectic.Construction.gaussianIntegral, one_mul] using! hlim.limUnder_eq.trans h.symm
  refine ⟨W, hW, hKW, ?_⟩
  rw [← integral_indicator W.isOpen.measurableSet, integral_selfDualMeasure,
    integral_indicator W.isOpen.measurableSet, ← hGval, Complex.real_smul, FunctionsMetaplectic.Construction.gaussianIndex, FunctionsMetaplectic.Construction.phase,
    nonarchimedean_gaussianIntegral_one_norm hNondiscrete ψ hu hc hn]
  simp only [Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

end

end OAI.RepresentationTheory.Weil.Local.GaussianNonarchimedean.Construction
