import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanNormCoordinates
import OAI.RepresentationTheory.Weil.UnitarySplitting.DiagonalNormGaussian

/-! # Archimedean Gaussian -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanGaussian.Construction

noncomputable section

/-! Absolutely convergent complex norm Gaussians and their boundary
values. Positive Haar normalization constants do not affect the phase. -/

open _root_.MeasureTheory _root_.Topology Filter

theorem complex_norm_gaussian (b : ℂ) (hb : 0 < b.re) :
    (∫ z : ℂ, Complex.exp (-b * (Complex.normSq z : ℂ))) = (Real.pi : ℂ) / b := by
  simp_rw [Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hh := GaussianFourier.integral_cexp_neg_mul_sq_norm (V := ℂ) hb
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2 : ℂ) ≠ 0),
    Complex.cpow_one] at hh
  exact hh

theorem norm_gaussian_from_complex_coordinates
    {E : Type} [NormedField E] [LocallyCompactSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (k : E ≃+* ℂ) (hk : Continuous k) (hki : Continuous k.symm)
    (q : E → ℝ) (hq : ∀ x, q x = Complex.normSq (k x))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℂ, 0 < b.re →
      (∫ x, Complex.exp (-b * (q x : ℂ)) ∂μ) = (C : ℂ) / b := by
  let e : E ≃ₜ+ ℂ :=
    { k.toAddEquiv with continuous_toFun := hk, continuous_invFun := hki }
  let ν : Measure ℂ := μ.map e
  let : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let c := Measure.addHaarScalarFactor ν (volume : Measure ℂ)
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume
  have hν : ν = c • volume := Measure.isAddLeftInvariant_eq_smul_of_regular ν volume
  refine ⟨(c : ℝ) * Real.pi, mul_pos hc Real.pi_pos, fun b hb => ?_⟩
  have heq : (∫ x, Complex.exp (-b * (q x : ℂ)) ∂μ) =
      ∫ z : ℂ, Complex.exp (-b * (Complex.normSq z : ℂ)) ∂ν := by
    change _ = ∫ z : ℂ, Complex.exp (-b * (Complex.normSq z : ℂ)) ∂μ.map e.toHomeomorph
    rw [e.toHomeomorph.isClosedEmbedding.integral_map]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change Complex.exp (-b * (q x : ℂ)) = Complex.exp (-b * (Complex.normSq (k x) : ℂ))
      rw [hq]
  rw [heq, hν, integral_smul_nnreal_measure, complex_norm_gaussian b hb,
    NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul, mul_div_assoc]

theorem gaussian_boundary_limit (C t : ℝ) (ht : t ≠ 0) :
    Tendsto (fun ε : ℝ => (C : ℂ) / ((ε : ℂ) - Complex.I * t)) (𝓝[>] (0 : ℝ))
      (𝓝 ((C : ℂ) / (-Complex.I * t))) := by
  have hden : (0 : ℂ) - Complex.I * (t : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht)))
  have hh : ContinuousAt (fun ε : ℝ => (C : ℂ) / ((ε : ℂ) - Complex.I * t)) 0 :=
    continuousAt_const.div (Complex.continuous_ofReal.continuousAt.sub continuousAt_const) hden
  have hh' := hh.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa only [Complex.ofReal_zero, zero_sub, neg_mul] using hh'

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanGaussian.Construction
