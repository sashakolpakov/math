import OAI.RepresentationTheory.Weil.Local.GaussianNonarchimedean
import OAI.RepresentationTheory.Weil.Local.GeneralGaussianMagnitude

/-! # General Gaussian Cutoff -/

namespace OAI.RepresentationTheory.Weil.Local.GeneralGaussianCutoff.Construction

noncomputable section

/-! Compact nonarchimedean Gaussian cutoffs with arbitrary nonzero coefficient. -/

open _root_.MeasureTheory

theorem nonarchimedean_gaussian_coefficient_normalized
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) (a : kˣ) :
    ((Real.sqrt (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ))⁻¹ : ℂ) * FunctionsMetaplectic.Construction.gaussianIntegral k ψ a.val =
      FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val * ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k a))⁻¹ : ℂ) := by
  have hs : (Real.sqrt (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (NonarchimedeanHaar.Construction.nonarchimedean_reference_scale hNondiscrete ψ hu hc hn).1).ne'
  have hm : (Real.sqrt (FunctionsMetaplectic.Construction.localModulus k a) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (FunctionsMetaplectic.Construction.localModulus_pos k a)).ne'
  rw [FunctionsMetaplectic.Construction.gaussianIndex, FunctionsMetaplectic.Construction.phase, GeneralGaussianMagnitude.Construction.nonarchimedean_gaussianIntegral_norm hNondiscrete ψ hu hc hn]
  push_cast
  field_simp

theorem exists_gaussian_coefficient_cutoff
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : kˣ) (K : Set k) (hK : IsCompact K) :
    ∃ W : OpenAddSubgroup k, IsCompact (W : Set k) ∧ K ⊆ W ∧
      (∫ x in (W : Set k), ψ (a.val * x ^ 2 / 2) ∂ FunctionsMetaplectic.Construction.selfDualMeasure k ψ) =
        FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val * ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k a))⁻¹ : ℂ) := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  obtain ⟨U, V, hU, hV, hVU, hphase, hdual, hradial, _⟩ :=
    GaussianCompact.Construction.exists_compactGaussian_domain hNondiscrete ψ hu hc hn a.val a.ne_zero
  obtain ⟨R, hR, hbound⟩ := (hK.union hU).isBounded.exists_pos_norm_le
  let W := IsUltrametricDist.closedBall_openAddSubgroup k hR
  have hKW : K ⊆ W := fun x hx => by
    change x ∈ Metric.closedBall 0 R
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound x (Or.inl hx)
  have hUW : U ≤ W := fun x hx => by
    change x ∈ Metric.closedBall 0 R
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound x (Or.inr hx)
  have hW : IsCompact (W : Set k) := isCompact_closedBall 0 R
  have hlim := GaussianCompact.Construction.regularizedGaussian_tendsto_compact_of_domain hNondiscrete ψ hu hc a.val
    U V hU hV hVU hphase hdual hradial
  have hGval : FunctionsMetaplectic.Construction.gaussianIntegral k ψ a.val =
      ∫ x in (W : Set k), ψ (a.val * x ^ 2 / 2) ∂(Measure.addHaar : Measure k) := by
    have h := GaussianCompact.Construction.compactGaussian_stabilizes_of_annihilator ψ hc Measure.addHaar a.val U V W hV hW
      hVU hUW hphase hdual
    exact hlim.limUnder_eq.trans h.symm
  refine ⟨W, hW, hKW, ?_⟩
  rw [← integral_indicator W.isOpen.measurableSet, GaussianNonarchimedean.Construction.integral_selfDualMeasure,
    integral_indicator W.isOpen.measurableSet, ← hGval, Complex.real_smul]
  simpa only [Complex.ofReal_inv] using
    nonarchimedean_gaussian_coefficient_normalized hNondiscrete ψ hu hc hn a

end

end OAI.RepresentationTheory.Weil.Local.GeneralGaussianCutoff.Construction
