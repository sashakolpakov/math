import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanReference
import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorFourier

/-! # Nonarchimedean Normalization -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanNormalization.LocalAnalysis

noncomputable section

/-! Exact Fourier inversion for the prescribed self-dual measure at a
nonarchimedean local field, in every rank. -/

open _root_.MeasureTheory
open scoped ENNReal

variable {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
  [MeasurableSpace k] [BorelSpace k] [ProperSpace k] [SecondCountableTopology k]
  [NonarchimedeanAddGroup k]
  (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ) (hn : ∃ t, ψ t ≠ 1)

include hu hc hn in
theorem nonarchimedean_fourier_square_reference (n : ℕ)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k)))
      (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))) f.val) x =
        ((Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ) ^ n : ℂ) * f.val (-x) := by
  obtain ⟨c, _, hSquare⟩ := FourierCompactDomain.LocalAnalysis.nonarchimedean_fourier_square_scalar n ψ hu hc hn
    (Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k)))
  let B := IsUltrametricDist.closedBall_openAddSubgroup k (by norm_num : (0 : ℝ) < 1)
  let φ : k → ℂ := (B : Set k).indicator (fun _ => 1)
  have hφc : IsLocallyConstant φ := CompactCharacter.LocalAnalysis.subgroup_indicator_locallyConstant B
  have hφs : HasCompactSupport φ := CompactCharacter.LocalAnalysis.subgroup_indicator_compactSupport B (isCompact_closedBall _ _)
  have hφ0 : φ 0 = 1 := Set.indicator_of_mem B.zero_mem _
  let g : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨TensorFourier.LocalAnalysis.tensorFunction n φ, TensorFourier.LocalAnalysis.tensorFunction_mem n hφc hφs⟩
  have hsc : TensorFourier.LocalAnalysis.scalarFourier ψ (Measure.addHaar : Measure k)
      (TensorFourier.LocalAnalysis.scalarFourier ψ (Measure.addHaar : Measure k) φ) 0 = (Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) := by
    simpa only [neg_zero, hφ0, mul_one] using TensorFourier.LocalAnalysis.scalarFourier_square_of_one_coordinate ψ
      (Measure.addHaar : Measure k) (Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ)
      (NonarchimedeanReference.LocalAnalysis.nonarchimedean_one_coordinate_normalization ψ hu hc hn).2 hφc hφs 0
  have he := hSquare g 0
  have hg0 : g.val (-0) = 1 := by simp [g, TensorFourier.LocalAnalysis.tensorFunction, hφ0]
  rw [hg0, mul_one] at he
  change Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k)))
      (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k)))
        (TensorFourier.LocalAnalysis.tensorFunction n φ)) 0 = (c : ℂ) at he
  rw [TensorFourier.LocalAnalysis.fourierIntegral_tensorFunction, TensorFourier.LocalAnalysis.fourierIntegral_tensorFunction] at he
  change (∏ _ : Fin n, TensorFourier.LocalAnalysis.scalarFourier ψ (Measure.addHaar : Measure k)
    (TensorFourier.LocalAnalysis.scalarFourier ψ (Measure.addHaar : Measure k) φ) 0) = (c : ℂ) at he
  simp only [hsc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at he
  rw [← he] at hSquare
  exact hSquare f x

omit [IsUltrametricDist k] [ProperSpace k] in
theorem positionMeasure_reference_scaling (n : ℕ) (hs : 0 < Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ) :
    Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ =
      ENNReal.ofReal ((Real.sqrt (Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ))⁻¹ ^ n) •
        Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k)) := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
    FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos k ψ hs
  unfold Local.FunctionsMetaplectic.Construction.positionMeasure
  refine Measure.pi_eq (μ := fun _ : Fin n => Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ) fun s _ => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Local.FunctionsMetaplectic.Construction.selfDualMeasure, Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (inv_nonneg.mpr (Real.sqrt_nonneg _))]

omit [IsUltrametricDist k] [ProperSpace k] in
theorem fourierIntegral_reference_scaling (n : ℕ) (hs : 0 < Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ)
    (f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ) f x =
      ((Real.sqrt (Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ))⁻¹ ^ n : ℝ) •
        Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))) f x := by
  rw [positionMeasure_reference_scaling ψ n hs, Local.FunctionsMetaplectic.Construction.fourierIntegral, integral_smul_measure]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rfl

include hu hc hn in
theorem nonarchimedean_fourier_inversion (n : ℕ)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ)
      (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val) x = f.val (-x) := by
  have hs := (NonarchimedeanReference.LocalAnalysis.nonarchimedean_one_coordinate_normalization ψ hu hc hn).1
  let a : ℝ := (Real.sqrt (Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ))⁻¹
  have hf : Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val =
      (a ^ n : ℂ) • Local.FunctionsMetaplectic.Construction.fourierIntegral ψ
        (Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))) f.val := by
    funext y
    rw [fourierIntegral_reference_scaling ψ n hs]
    simp only [a, Complex.real_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow, Complex.ofReal_inv]
  rw [fourierIntegral_reference_scaling ψ n hs, hf, Local.FunctionsMetaplectic.Construction.fourierIntegral_smul,
    Pi.smul_apply, nonarchimedean_fourier_square_reference ψ hu hc hn]
  have hbase : a * a * Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ = 1 := by
    have hr : Real.sqrt (Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
    calc
      _ = a * a * (Real.sqrt (Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ) *
          Real.sqrt (Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ)) := by rw [Real.mul_self_sqrt hs.le]
      _ = 1 := by dsimp [a]; field_simp
  have hcoef : a ^ n * a ^ n * Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ ^ n = 1 := by
    rw [← mul_pow, ← mul_pow, hbase, one_pow]
  have hcoefC : (a ^ n : ℂ) * (a ^ n : ℂ) * (Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) ^ n = 1 := by
    exact_mod_cast hcoef
  change (a ^ n : ℝ) • ((a ^ n : ℂ) *
    ((Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) ^ n * f.val (-x))) = _
  rw [Complex.real_smul]
  push_cast
  rw [← mul_assoc, ← mul_assoc, hcoefC, one_mul]

/-- The exact raw Fourier lift at a nonarchimedean field. Its Haar measure
is the one defined in the accepted statement through the reference compact. -/
def nonarchimedeanRawFourierOscillator [CharZero k] (n : ℕ) : Local.FunctionsMetaplectic.Construction.Oscillator k n ψ := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
    FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos k ψ
      (NonarchimedeanReference.LocalAnalysis.nonarchimedean_one_coordinate_normalization ψ hu hc hn).1
  let : (Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ).IsAddHaarMeasure := by unfold Local.FunctionsMetaplectic.Construction.positionMeasure; infer_instance
  exact FourierIntertwiner.LocalAnalysis.fourierOscillator ψ hu hc (Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ)
    (NonarchimedeanIntertwiner.LocalAnalysis.nonarchimedean_fourier_mem ψ hu hc hn (Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ))
    (nonarchimedean_fourier_inversion ψ hu hc hn n)

theorem nonarchimedeanRawFourierOscillator_apply [CharZero k] (n : ℕ)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    ((nonarchimedeanRawFourierOscillator ψ hu hc hn n).val.2 f).val x =
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x := rfl

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanNormalization.LocalAnalysis
