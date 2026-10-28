import OAI.RepresentationTheory.Theta.Adelic.LeviWeakIntegral
import OAI.RepresentationTheory.Theta.Adelic.LocalWeylIntegrability

/-! # Levi Weak Normalization -/

namespace OAI.RepresentationTheory.Theta.Adelic.LeviWeakNormalization

noncomputable section

/-! The actual positive Levi oscillator has exactly the corrected weak
Cayley normalization over every characteristic-zero local field. -/

open _root_.MeasureTheory
open scoped NNReal ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.LeviCayleyPhase OAI.RepresentationTheory.Theta.Adelic.LeviCayleyPhase.Scale OAI.RepresentationTheory.Theta.Adelic.LeviWeakIntegral
open OAI.RepresentationTheory.Theta.Adelic.LocalWeylIntegrability OAI.RepresentationTheory.Theta.Adelic.FieldWeylTransport

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (N : ℕ)
variable (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
variable (hc : Continuous ψ) (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1)
variable (A U : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) (hU : U.val = A.val - 1)

theorem positive_scale_identity (a u : ℝ) (ha : 0 < a) (hu : 0 < u) :
    (u / Real.sqrt a)⁻¹ * (u / a) = (Real.sqrt a)⁻¹ := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq := Real.sq_sqrt ha.le
  field_simp
  nlinarith

include hU in
omit [CompleteSpace k] [CharZero k] [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] in
theorem levi_normalizing_coefficient :
    (Weil.AdelicSplitting.Normalization.Construction.openCellScale k N (Weil.Local.Generators.Construction.leviSymplectic A) : ℂ)⁻¹ *
      (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k U) / Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ) =
        ((Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A)))⁻¹ : ℂ) := by
  rw [LeviCayleyPhase.Scale.openCellScale_levi N A U hU]
  exact_mod_cast positive_scale_identity
    (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A)) (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k U))
    (Weil.Local.FunctionsMetaplectic.Construction.localModulus_pos k _) (Weil.Local.FunctionsMetaplectic.Construction.localModulus_pos k _)

include hnd hc hu hn hU in
theorem positiveLevi_corrected_weak (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (Weil.AdelicSplitting.NormalizationLevi.Construction.localLeviHom N ψ A) f).val x * conj (h.val x)
      ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) =
    Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k N ψ (Weil.Local.Generators.Construction.leviSymplectic A) f.val h.val := by
  let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
    (Weil.Local.Analytic.Construction.localField_analytic_normalization hnd ψ hc hu hn N).2.1
  let μ := Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ
  let : μ.IsAddHaarMeasure := by dsimp [μ, Weil.Local.FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  let ν := Measure.pi (fun _ : Fin N ⊕ Fin N => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ)
  let Q := Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase k N (Weil.Local.Generators.Construction.leviSymplectic A) (LeviCayleyPhase.levi_openCell N A U hU)
  let c := Measure.addHaarScalarFactor (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) μ
  have href : Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N = c • μ := Measure.isAddLeftInvariant_eq_smul _ _
  have hi := LocalWeylIntegrability.local_weak_phase_integrable hnd ψ hc hu hn μ ν Q
    (Weil.AdelicSplitting.CorrectedWeakAnalysis.Construction.schrodingerCayleyPhase_continuous N (Weil.Local.Generators.Construction.leviSymplectic A) (LeviCayleyPhase.levi_openCell N A U hU)) f h
  have hbase := LeviWeakIntegral.weakWeyl_levi_integral N hnd ψ hc hu hn A U hU f h hi
  have hrefint : (∫ x, f.val ((A⁻¹).val.mulVec x) * conj (h.val x) ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) =
      (c : ℂ) * ∫ x, f.val ((A⁻¹).val.mulVec x) * conj (h.val x) ∂μ := by
    rw [href, integral_smul_nnreal_measure]
    rfl
  have hop : (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (Weil.AdelicSplitting.NormalizationLevi.Construction.localLeviHom N ψ A) f).val x * conj (h.val x)
      ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) =
      ((Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A)))⁻¹ : ℂ) *
        ∫ x, f.val ((A⁻¹).val.mulVec x) * conj (h.val x) ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N := by
    change (∫ x, ((Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ A).val.2 f).val x * conj (h.val x)
      ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) = _
    simp_rw [Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator_apply, mul_assoc]
    exact integral_const_mul _ _
  rw [hop, hrefint, Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue_open k N ψ (Weil.Local.Generators.Construction.leviSymplectic A) (LeviCayleyPhase.levi_openCell N A U hU)]
  unfold Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCell
  rw [href, FieldWeylTransport.weakWeylGaussian_smul_position, hbase]
  rw [← levi_normalizing_coefficient N A U hU]
  ring

end

end OAI.RepresentationTheory.Theta.Adelic.LeviWeakNormalization
