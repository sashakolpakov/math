import OAI.RepresentationTheory.Theta.Adelic.CayleyConjugation
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylCoefficients
import OAI.RepresentationTheory.Weil.Local.Analytic

/-! # Weak Cayley Conjugation -/

namespace OAI.RepresentationTheory.Theta.Adelic.WeakCayleyConjugation

noncomputable section

/-! Exact covariance of the corrected weak Cayley pairing under actual
oscillator changes of polarization. -/

open _root_.MeasureTheory

open OAI.RepresentationTheory.Weil.Local.Analytic.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction
open OAI.RepresentationTheory.Theta.Adelic.CayleyConjugation

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (N : ℕ)
variable (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
variable (hc : Continuous ψ) (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1)

def symplecticHomeomorph (b : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N ≃ₜ Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N where
  toEquiv := (Weil.AdelicSplitting.SchrodingerPairing.Construction.symplecticPhaseEquiv k N b).toEquiv
  continuous_toFun := LinearMap.continuous_on_pi (Weil.AdelicSplitting.SchrodingerPairing.Construction.symplecticPhaseEquiv k N b).toLinearMap
  continuous_invFun := LinearMap.continuous_on_pi (Weil.AdelicSplitting.SchrodingerPairing.Construction.symplecticPhaseEquiv k N b).symm.toLinearMap

include hnd hc hu hn in
theorem correctedWeakOpenCellValue_conjugate (w : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N)
    (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k N ψ
      (Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ w * g * (Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ w)⁻¹)
        (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w f).val (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w h).val =
      Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k N ψ g f.val h.val := by
  let b := Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ w
  let T := Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ w
  have hd := CayleyConjugation.conjugate_difference_det N b g
  by_cases hg : (g.val - 1).det ≠ 0
  · have hbg : ((b * g * b⁻¹).val - 1).det ≠ 0 := hd.trans_ne hg
    rw [Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue_open k N ψ _ hbg,
      Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue_open k N ψ g hg]
    unfold Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCell
    rw [CayleyConjugation.openCellScale_conjugate]
    congr 1
    let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
      (Weil.Local.Analytic.Construction.localField_analytic_normalization hnd ψ hc hu hn N).2.1
    have hp := Weil.AdelicSplitting.PhaseMeasure.Construction.symplecticAction_measurePreserving k N (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ) b
    have he : MeasurableEmbedding (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction b) :=
      (symplecticHomeomorph N b).toMeasurableEquiv.measurableEmbedding
    unfold Weil.UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian
    rw [← hp.integral_comp he]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      change ψ (Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase k N (b * g * b⁻¹) hbg (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction b v)) *
        Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
          (T f).val (T h).val (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction b v) = _
      rw [CayleyConjugation.cayleyPhase_conjugate N b g hg hbg]
      congr 1
      exact Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_covariance hnd ψ hc hu T w.property.1
        (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction b) (Weil.AdelicSplitting.ArchimedeanWeylCoefficients.LocalAnalysis.localOscillator_heisenberg_covariance hnd ψ hc hu w) f h v
  · have hbg : ¬ ((b * g * b⁻¹).val - 1).det ≠ 0 := by rw [hd]; exact hg
    rw [Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue, dite_eq_right hbg, Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue, dite_eq_right hg]

end

end OAI.RepresentationTheory.Theta.Adelic.WeakCayleyConjugation
