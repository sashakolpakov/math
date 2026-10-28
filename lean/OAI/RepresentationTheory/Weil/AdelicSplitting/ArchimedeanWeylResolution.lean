import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylAnalysis
import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylSynthesisAnalysis

/-! # Archimedean Weyl Resolution -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylResolution.Construction

noncomputable section

/-! Exact archimedean reconstruction from Weyl coefficients. The output
is identified with the original Bruhat function by proved test pairings. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
variable (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (W : Oscillator.Construction.LocalCover k N ψ) (hW : Oscillator.Construction.localProjection k N ψ W = Local.Generators.Construction.weylSymplectic k N)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure] (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N)

include hk hc hu W hW

theorem archimedeanWeylAnalysis_continuous (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    Continuous (UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val) :=
  (ArchimedeanWeylCoefficients.LocalAnalysis.archimedeanWeylCoefficientRapid hk ψ hc hu W hW u f).continuous.star

theorem archimedeanWeylAnalysis_integrable (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    Integrable (UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val) ν :=
  memLp_one_iff_integrable.mp
    ((memLp_one_iff_integrable.mpr
      ((ArchimedeanWeylCoefficients.LocalAnalysis.archimedeanWeylCoefficientRapid hk ψ hc hu W hW u f).integrable ν)).star)

variable (hMoyal : ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
  (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val v‖ ^ 2 ∂ν) =
    Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N h)

include hMoyal in
theorem archimedeanWeylResolution (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    UnitarySplitting.WeylSynthesisAdd.Construction.weylSynthesis ψ ν (UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val) u.val =
      fun x => (Local.FunctionsMetaplectic.Construction.l2Energy k N u : ℂ) * f.val x := by
  have ha := archimedeanWeylAnalysis_continuous hk ψ hc hu W hW u f
  have hai := archimedeanWeylAnalysis_integrable hk ψ hc hu W hW ν u f
  apply WeylSynthesisAnalysis.Construction.continuous_eq_of_bruhat_pairings (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
    _ _ (WeylSynthesisAnalysis.Construction.weylSynthesis_continuous ψ hc hu ν _ ha hai u)
    (continuous_const.mul (TestSpace.LocalAnalysis.schwartzBruhat_continuous f.property))
  intro h
  rw [UnitarySplitting.WeylSynthesis.Construction.weylSynthesis_pairing ψ hc hu (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) ν _ ha hai u h]
  have hp := ArchimedeanWeylAnalysis.Construction.archimedeanWeylAnalysis_pairing hk ψ hc hu W hW ν u hMoyal h f
  have he (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
      conj (UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val h.val v) =
        UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val h.val v := by
    simp only [UnitarySplitting.WeylAnalysis.Construction.weylAnalysis, starRingEnd_self_apply]
  simp_rw [he] at hp
  rw [hp, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (Local.FunctionsMetaplectic.Construction.l2Energy k N u : ℂ) * (f.val x * conj (h.val x)) =
      ((Local.FunctionsMetaplectic.Construction.l2Energy k N u : ℂ) * f.val x) * conj (h.val x)
    ring

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylResolution.Construction
