import OAI.RepresentationTheory.Theta.Adelic.WeakCayleyConjugation
import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak

/-! # Normalization Conjugation -/

namespace OAI.RepresentationTheory.Theta.Adelic.NormalizationConjugation

noncomputable section

/-! Transport of an exact weak normalization through an actual unitary
oscillator change of polarization. -/

open _root_.MeasureTheory
open scoped ComplexConjugate InnerProductSpace

open OAI.RepresentationTheory.Weil.UnitarySplitting.Weak.Construction (testToL2 testToL2_inner energy_preserving_inner)
open OAI.RepresentationTheory.Theta.Adelic.WeakCayleyConjugation

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (N : ℕ) (ψ : AddChar k ℂ)

omit [CompleteSpace k] [CharZero k] in
theorem operator_pairing_conjugate (w a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (w * a * w⁻¹) (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w f)).val x *
      conj ((Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w h).val x) ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) =
    ∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f).val x * conj (h.val x)
      ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N := by
  rw [← Weil.UnitarySplitting.Weak.Construction.testToL2_inner, ← Weil.UnitarySplitting.Weak.Construction.testToL2_inner]
  rw [map_mul, map_mul, map_inv]
  change ⟪Weil.UnitarySplitting.Weak.Construction.testToL2 k N (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w h),
      Weil.UnitarySplitting.Weak.Construction.testToL2 k N (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w
        (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a ((Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w).symm (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w f))))⟫_ℂ = _
  rw [LinearEquiv.symm_apply_apply]
  exact Weil.UnitarySplitting.Weak.Construction.energy_preserving_inner k N (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w).toLinearMap w.property.1 h
    (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f)

theorem weak_normalization_pullback (hnd : ¬ DiscreteTopology k)
    (hc : Continuous ψ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hn : ∃ t : k, ψ t ≠ 1)
    (w a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (c : ℂ)
    (hformula : ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
      (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (w * a * w⁻¹) f).val x * conj (h.val x)
        ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) =
      c * Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k N ψ
        (Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ w * g * (Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ w)⁻¹) f.val h.val)
    (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f).val x * conj (h.val x)
      ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) =
        c * Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k N ψ g f.val h.val := by
  rw [← operator_pairing_conjugate N ψ w a f h, hformula,
    WeakCayleyConjugation.correctedWeakOpenCellValue_conjugate N hnd ψ hc hu hn]

end

end OAI.RepresentationTheory.Theta.Adelic.NormalizationConjugation
