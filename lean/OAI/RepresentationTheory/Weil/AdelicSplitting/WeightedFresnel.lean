import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalFresnel
import OAI.RepresentationTheory.Weil.AdelicSplitting.ScalarLeviNormalization

/-! # Weighted Fresnel -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedFresnel.LocalAnalysis

noncomputable section

/-! Exact local Fourier-quadratic relation for every nonzero scalar
coefficient, obtained by rescaling the character and the input. -/

open _root_.MeasureTheory

theorem localField_weighted_fresnel
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) (N : ℕ) (ψ : AddChar k ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (b : k) (hb : b ≠ 0) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (x : Local.FunctionsMetaplectic.Construction.Position k N) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ)
      (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (b • 1) (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ) f.val)) x =
      Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ b ^ N * ((Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ))⁻¹ : ℂ) ^ N *
        ψ (Local.FunctionsMetaplectic.Construction.quadratic ((-b⁻¹) • 1) x) *
          Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ) (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ ((-b⁻¹) • 1) f.val) (b⁻¹ • x) := by
  let : SecondCountableTopology k := TestSpace.LocalAnalysis.localField_secondCountable k hnd
  have hs := (Local.Analytic.Construction.localField_analytic_normalization hnd ψ hc hu hn N).1
  let η := ψ.mulShift b
  have hηc : Continuous η := hc.comp (continuous_const.mul continuous_id)
  have hηu : ∀ t, ‖η t‖ = 1 := fun t => hu (b * t)
  have hηn : ∃ t, η t ≠ 1 := by
    obtain ⟨t, ht⟩ := hn
    refine ⟨b⁻¹ * t, ?_⟩
    simpa only [η, AddChar.mulShift_apply, ← mul_assoc, mul_inv_cancel₀ hb, one_mul] using ht
  let e := CharacterScaling.LocalAnalysis.scalarPositionEquiv N b hb
  let g : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := ⟨fun y => f.val (b • y),
    FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv e.toContinuousAddEquiv f.property⟩
  let Fψ := Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ)
  let Fη := Local.FunctionsMetaplectic.Construction.fourierIntegral η (Local.FunctionsMetaplectic.Construction.positionMeasure k N η)
  let s : ℂ := (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) : ℂ) ^ N
  let t : ℂ := ((Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ))⁻¹ : ℂ) ^ N
  have hst : t * s = 1 := by
    have hz : (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (DeterminantMeasure.LocalAnalysis.haarModulus_pos k hb)).ne'
    simp only [t, s, ← mul_pow, inv_mul_cancel₀ hz, one_pow]
  have hgin : Fη g.val = t • Fψ f.val := by
    funext y
    simpa only [Complex.ofReal_inv] using! FourierCharacterScaling.LocalAnalysis.fourier_selfDual_mulShift_scaled_input N ψ b hb hs f.val y
  have hQ : Local.FunctionsMetaplectic.Construction.quadraticOperator η 1 (Fψ f.val) = Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (b • 1) (Fψ f.val) :=
    ScalarLeviNormalization.LocalAnalysis.quadraticOperator_mulShift_one N ψ b _
  have hFout : Fη (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (b • 1) (Fψ f.val)) (b⁻¹ • x) =
      s * Fψ (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (b • 1) (Fψ f.val)) x := by
    have hh := FourierCharacterScaling.LocalAnalysis.fourier_selfDual_mulShift N ψ b hb hs (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (b • 1) (Fψ f.val)) (b⁻¹ • x)
    simpa only [smul_smul, mul_inv_cancel₀ hb, one_smul] using! hh
  have hneg : Local.FunctionsMetaplectic.Construction.quadraticOperator η (-1) g.val =
      fun y => Local.FunctionsMetaplectic.Construction.quadraticOperator ψ ((-b⁻¹) • 1) f.val (b • y) :=
    ScalarLeviNormalization.LocalAnalysis.quadraticOperator_mulShift_neg_scaled N ψ b hb f.val
  have hFin : Fη (Local.FunctionsMetaplectic.Construction.quadraticOperator η (-1) g.val) (b⁻¹ • x) =
      t * Fψ (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ ((-b⁻¹) • 1) f.val) (b⁻¹ • x) := by
    rw [hneg]
    simpa only [Complex.ofReal_inv] using! FourierCharacterScaling.LocalAnalysis.fourier_selfDual_mulShift_scaled_input N ψ b hb hs
      (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ ((-b⁻¹) • 1) f.val) (b⁻¹ • x)
  have hFsmul (φ : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) : Fη (t • φ) = t • Fη φ :=
    Local.FunctionsMetaplectic.Construction.fourierIntegral_smul η _ t φ
  have hh := LocalFresnel.Analysis.localField_fresnel hnd N η hηc hηu hηn g (b⁻¹ • x)
  change Fη (Local.FunctionsMetaplectic.Construction.quadraticOperator η 1 (Fη g.val)) (b⁻¹ • x) =
    Local.FunctionsMetaplectic.Construction.gaussianIndex k η 1 ^ N * η (-Local.FunctionsMetaplectic.Construction.quadratic 1 (b⁻¹ • x)) * Fη (Local.FunctionsMetaplectic.Construction.quadraticOperator η (-1) g.val) (b⁻¹ • x) at hh
  rw [hgin, map_smul, hFsmul, Pi.smul_apply, smul_eq_mul, hQ, hFout,
    ← mul_assoc, hst, one_mul, hFin] at hh
  have hγ : Local.FunctionsMetaplectic.Construction.gaussianIndex k η 1 = Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ b := by
    simpa only [mul_one] using FourierCharacterScaling.LocalAnalysis.gaussianIndex_mulShift k ψ b 1
  rw [hγ, ScalarLeviNormalization.LocalAnalysis.mulShift_negative_quadratic_scaled N ψ b hb] at hh
  change Fψ (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (b • 1) (Fψ f.val)) x = _
  rw [hh]
  ring

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedFresnel.LocalAnalysis
