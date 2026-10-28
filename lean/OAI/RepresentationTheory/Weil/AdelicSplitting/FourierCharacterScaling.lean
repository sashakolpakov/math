import OAI.RepresentationTheory.Weil.AdelicSplitting.ScalarPlancherel
import OAI.RepresentationTheory.Weil.AdelicSplitting.Annihilator

/-! # Fourier Character Scaling -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Weil.AdelicSplitting.FourierCharacterScaling

/-! Character rescaling transports the actual Gaussian phase and scales
the prescribed self-dual measure by the positive square root modulus. -/

open _root_.MeasureTheory

namespace LocalAnalysis

variable (k : Type) [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k ℂ)

theorem regularizedGaussian_mulShift (b a : k) (ε : ℝ) :
    Local.FunctionsMetaplectic.Construction.regularizedGaussian k (ψ.mulShift b) a ε = Local.FunctionsMetaplectic.Construction.regularizedGaussian k ψ (b * a) ε := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (Real.exp (-ε * ‖x‖ ^ 2) : ℂ) * ψ (b * (a * x ^ 2 / 2)) =
      (Real.exp (-ε * ‖x‖ ^ 2) : ℂ) * ψ ((b * a) * x ^ 2 / 2)
    rw [show b * (a * x ^ 2 / 2) = (b * a) * x ^ 2 / 2 by ring]

theorem gaussianIntegral_mulShift (b a : k) :
    Local.FunctionsMetaplectic.Construction.gaussianIntegral k (ψ.mulShift b) a = Local.FunctionsMetaplectic.Construction.gaussianIntegral k ψ (b * a) := by
  unfold Local.FunctionsMetaplectic.Construction.gaussianIntegral
  congr 1
  funext ε
  exact regularizedGaussian_mulShift k ψ b a ε

theorem gaussianIndex_mulShift (b a : k) :
    Local.FunctionsMetaplectic.Construction.gaussianIndex k (ψ.mulShift b) a = Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (b * a) := by
  rw [Local.FunctionsMetaplectic.Construction.gaussianIndex, gaussianIntegral_mulShift]
  rfl

end LocalAnalysis

namespace Construction

variable (F : Type) [Field F] [NumberField F] (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

theorem localAdditiveCharacter_mulShift_principal (q : F) (v : ArchimedeanAdeles.Construction.Places F) :
    Characters.Construction.localAdditiveCharacter F (ψ.mulShift (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q)) v =
      (Characters.Construction.localAdditiveCharacter F ψ v).mulShift (ArchimedeanAdeles.Construction.rationalScalar F v q) := by
  ext t
  change ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q * ArchimedeanAdeles.Construction.localAdd F v t) =
    ψ (ArchimedeanAdeles.Construction.localAdd F v (ArchimedeanAdeles.Construction.rationalScalar F v q * t))
  rw [Annihilator.Construction.adelic_mul_localAdd]
  rfl

end Construction

end RepresentationTheory.Weil.AdelicSplitting.FourierCharacterScaling

namespace RepresentationTheory.Weil.AdelicSplitting.FourierCharacterScaling.LocalAnalysis

/-! Exact Fourier formulas for a rescaled central character and for a
simultaneously rescaled input, with the prescribed self-dual measures. -/

open _root_.MeasureTheory

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
variable (N : ℕ) (ψ : AddChar k ℂ) (b : k) (hb : b ≠ 0)
variable (hs : 0 < Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ)

include hb hs

theorem positionMeasure_mulShift :
    Local.FunctionsMetaplectic.Construction.positionMeasure k N (ψ.mulShift b) =
      ENNReal.ofReal (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) ^ N) • Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos k ψ hs
  have hsp : 0 < Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k (ψ.mulShift b) := by
    rw [CharacterScaling.LocalAnalysis.fourierHaarScaleSquared_mulShift ψ b hb]
    exact div_pos hs (DeterminantMeasure.LocalAnalysis.haarModulus_pos k hb)
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure k (ψ.mulShift b)).IsAddHaarMeasure :=
    FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos k (ψ.mulShift b) hsp
  unfold Local.FunctionsMetaplectic.Construction.positionMeasure
  refine Measure.pi_eq (μ := fun _ : Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure k (ψ.mulShift b)) fun s _ => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [ScalarPlancherel.LocalAnalysis.selfDualMeasure_mulShift ψ hs b hb, Measure.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (Real.sqrt_nonneg _)]

theorem fourier_selfDual_mulShift (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k N) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.mulShift b) (Local.FunctionsMetaplectic.Construction.positionMeasure k N (ψ.mulShift b)) f x =
      (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) ^ N : ℂ) *
        Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ) f (b • x) := by
  rw [positionMeasure_mulShift N ψ b hb hs, Local.FunctionsMetaplectic.Construction.fourierIntegral, integral_smul_measure,
    ENNReal.toReal_ofReal (pow_nonneg (Real.sqrt_nonneg _) N)]
  change (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) ^ N : ℝ) •
    Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.mulShift b) (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ) f x = _
  rw [CharacterScaling.LocalAnalysis.fourierIntegral_mulShift, Complex.real_smul]
  rw [Complex.ofReal_pow]

theorem fourier_selfDual_mulShift_scaled_input (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k N) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.mulShift b) (Local.FunctionsMetaplectic.Construction.positionMeasure k N (ψ.mulShift b)) (fun y => f (b • y)) x =
      ((Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ))⁻¹ ^ N : ℂ) *
        Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ) f x := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos k ψ hs
  rw [positionMeasure_mulShift N ψ b hb hs, Local.FunctionsMetaplectic.Construction.fourierIntegral, integral_smul_measure,
    ENNReal.toReal_ofReal (pow_nonneg (Real.sqrt_nonneg _) N)]
  change (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) ^ N : ℝ) •
    Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.mulShift b) (Measure.pi (fun _ : Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ))
      (fun y => f (b • y)) x = _
  rw [CharacterScaling.LocalAnalysis.fourierIntegral_mulShift_scaled_input N ψ b hb (Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ), smul_smul, Complex.real_smul]
  have hp : 0 < (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) := DeterminantMeasure.LocalAnalysis.haarModulus_pos k hb
  have he : Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) * (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ)⁻¹ =
      (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ))⁻¹ := by
    have hsq := Real.mul_self_sqrt hp.le
    have hz : Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    calc
      _ = Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) *
          (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) * Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ))⁻¹ :=
        congrArg (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) * ·) (congrArg Inv.inv hsq.symm)
      _ = _ := by field_simp
  rw [← inv_pow, ← mul_pow, he]
  simp only [Complex.ofReal_pow, Complex.ofReal_inv, Local.FunctionsMetaplectic.Construction.positionMeasure]

end RepresentationTheory.Weil.AdelicSplitting.FourierCharacterScaling.LocalAnalysis

end

end OAI
