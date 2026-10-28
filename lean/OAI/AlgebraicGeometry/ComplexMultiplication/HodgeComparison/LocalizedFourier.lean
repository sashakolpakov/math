import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization

/-! # Localized Fourier -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalizedFourier.CM.Construction

noncomputable section

/-! Compact frequency truncations of functions supported in a fixed compact spatial domain. -/

open _root_.MeasureTheory FourierTransform Set
open scoped SchwartzMap BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {K B : Set E} [CompactSpace K] [CompactSpace B]
  [IsFiniteMeasure ((volume : Measure E).comap (Subtype.val : K → E))]
  [IsFiniteMeasure ((volume : Measure E).comap (Subtype.val : B → E))]

/-- The compact integral kernel, with both arguments identified with their ambient positions. -/
def spatialFrequencyKernelMap :
    Lp ℂ 2 ((volume : Measure E).comap (Subtype.val : K → E)) →L[ℂ]
      Lp ℂ 2 ((volume : Measure E).comap (Subtype.val : B → E)) :=
  CompactFourier.CM.Construction.compactFourierLpMap _ _ ⟨Subtype.val, continuous_subtype_val⟩
    ⟨Subtype.val, continuous_subtype_val⟩

theorem spatialFrequencyKernelMap_isCompact :
    IsCompactOperator (spatialFrequencyKernelMap (K := K) (B := B)) :=
  CompactFourier.CM.Construction.compactFourierLpMap_isCompact _ _ _ _

/-- This ambient L² operator first truncates space, then frequency, and then transforms back. -/
def localizedFourierMap (hK : MeasurableSet K) (hB : MeasurableSet B) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (Lp.fourierTransformₗᵢ E ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((LpLocalization.CM.Construction.lpSubtypeZeroExtension volume hB).toContinuousLinearMap.comp
      ((spatialFrequencyKernelMap (K := K) (B := B)).comp
        (LpLocalization.CM.Construction.lpSubtypeRestriction volume hK)))

theorem localizedFourierMap_isCompact (hK : MeasurableSet K) (hB : MeasurableSet B) :
    IsCompactOperator (localizedFourierMap hK hB) :=
  (((spatialFrequencyKernelMap_isCompact (K := K) (B := B)).comp_clm
    (LpLocalization.CM.Construction.lpSubtypeRestriction volume hK)).clm_comp
    (LpLocalization.CM.Construction.lpSubtypeZeroExtension volume hB).toContinuousLinearMap).clm_comp
    (Lp.fourierTransformₗᵢ E ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap

omit [IsFiniteMeasure ((volume : Measure E).comap (Subtype.val : B → E))] in
theorem compactFourierMap_schwartz_support (hK : MeasurableSet K)
    (f : 𝓢(E, ℂ)) (hf : Function.support f ⊆ K) (y : B) :
    CompactFourier.CM.Construction.compactFourierMap (E := E) (X := K) (Y := B) ((volume : Measure E).comap (Subtype.val : K → E))
      ⟨Subtype.val, continuous_subtype_val⟩ ⟨Subtype.val, continuous_subtype_val⟩
      (LpLocalization.CM.Construction.lpSubtypeRestriction volume hK (f.toLp 2 (volume : Measure E))) y = (𝓕 f) y.val := by
  rw [CompactFourier.CM.Construction.compactFourierMap_apply]
  have hae : LpLocalization.CM.Construction.lpSubtypeRestriction volume hK (f.toLp 2 (volume : Measure E)) =ᵐ[
      (volume : Measure E).comap (Subtype.val : K → E)] (fun x : K => f x.val) :=
    (LpLocalization.CM.Construction.lpSubtypeRestriction_coeFn volume hK (f.toLp 2 (volume : Measure E))).trans
      ((ae_restrict_iff_subtype hK).mp (ae_restrict_of_ae (f.coeFn_toLp 2 (volume : Measure E))))
  calc
    _ = ∫ x : K, Complex.exp
        ((-2 * Real.pi * inner ℝ x.val y.val : ℝ) * Complex.I) * f x.val
        ∂((volume : Measure E).comap (Subtype.val : K → E)) := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]
      rfl
    _ = ∫ x in K, Complex.exp
        ((-2 * Real.pi * inner ℝ x y.val : ℝ) * Complex.I) * f x :=
      integral_subtype_comap (μ := (volume : Measure E)) hK
        (fun x : E => Complex.exp
          ((-2 * Real.pi * inner ℝ x y.val : ℝ) * Complex.I) * f x)
    _ = ∫ x, Complex.exp
        ((-2 * Real.pi * inner ℝ x y.val : ℝ) * Complex.I) * f x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : f x = 0 := by
        by_contra hne
        exact hx (hf hne)
      rw [hz, mul_zero]
    _ = (𝓕 f) y.val := by
      rw [SchwartzMap.fourier_coe, Real.fourier_eq']
      rfl
  rfl

theorem spatialFrequencyKernelMap_schwartz_support (hK : MeasurableSet K)
    (hB : MeasurableSet B) (f : 𝓢(E, ℂ)) (hf : Function.support f ⊆ K) :
    spatialFrequencyKernelMap (LpLocalization.CM.Construction.lpSubtypeRestriction volume hK (f.toLp 2 (volume : Measure E))) =
      LpLocalization.CM.Construction.lpSubtypeRestriction volume hB (𝓕 (f.toLp 2 (volume : Measure E))) := by
  apply Lp.ext
  have hout := BoundedContinuousFunction.coeFn_toLp (𝕜 := ℂ) (p := 2)
    (μ := (volume : Measure E).comap (Subtype.val : B → E))
    (CompactFourier.CM.Construction.compactFourierMap (E := E) (X := K) (Y := B) ((volume : Measure E).comap (Subtype.val : K → E))
      ⟨Subtype.val, continuous_subtype_val⟩ ⟨Subtype.val, continuous_subtype_val⟩
      (LpLocalization.CM.Construction.lpSubtypeRestriction volume hK (f.toLp 2 (volume : Measure E))))
  have hin := LpLocalization.CM.Construction.lpSubtypeRestriction_coeFn volume hB (𝓕 (f.toLp 2 (volume : Measure E)))
  have hfour : ∀ᵐ y : B ∂((volume : Measure E).comap (Subtype.val : B → E)),
      (𝓕 (f.toLp 2 (volume : Measure E))) y.val = (𝓕 f) y.val := by
    rw [SchwartzMap.toLp_fourier_eq]
    exact (ae_restrict_iff_subtype hB).mp (ae_restrict_of_ae ((𝓕 f).coeFn_toLp 2 (volume : Measure E)))
  have hout' : spatialFrequencyKernelMap (LpLocalization.CM.Construction.lpSubtypeRestriction volume hK (f.toLp 2 volume))
      =ᵐ[(volume : Measure E).comap (Subtype.val : B → E)]
      (CompactFourier.CM.Construction.compactFourierMap (E := E) (X := K) (Y := B)
        ((volume : Measure E).comap (Subtype.val : K → E))
        ⟨Subtype.val, continuous_subtype_val⟩ ⟨Subtype.val, continuous_subtype_val⟩
        (LpLocalization.CM.Construction.lpSubtypeRestriction volume hK (f.toLp 2 volume))) := hout
  filter_upwards [hout', hin, hfour] with y hy hi hf'
  exact hy.trans ((compactFourierMap_schwartz_support hK f hf y).trans (hi.trans hf').symm)

theorem localizedFourierMap_schwartz_support (hK : MeasurableSet K)
    (hB : MeasurableSet B) (f : 𝓢(E, ℂ)) (hf : Function.support f ⊆ K) :
    localizedFourierMap hK hB (f.toLp 2 (volume : Measure E)) =
      𝓕⁻ (LpLocalization.CM.Construction.lpSubtypeZeroExtension volume hB (LpLocalization.CM.Construction.lpSubtypeRestriction volume hB (𝓕 (f.toLp 2 (volume : Measure E))))) := by
  change 𝓕⁻ (LpLocalization.CM.Construction.lpSubtypeZeroExtension volume hB
    (spatialFrequencyKernelMap (LpLocalization.CM.Construction.lpSubtypeRestriction volume hK (f.toLp 2 (volume : Measure E))))) = _
  rw [spatialFrequencyKernelMap_schwartz_support hK hB f hf]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalizedFourier.CM.Construction
