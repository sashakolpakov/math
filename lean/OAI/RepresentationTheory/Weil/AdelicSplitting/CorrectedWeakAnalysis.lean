import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylCoefficients
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.RealNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexNormalization

/-! # Corrected Weak Analysis -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedWeakAnalysis

noncomputable section

/-! Absolute convergence of the corrected weak open-cell integral at
archimedean places, derived from the actual Fourier oscillator. -/

open _root_.MeasureTheory

namespace Local

theorem archimedean_weak_phase_integrable
    {k : Type} [NormedField k] [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
    [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
    (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (a : Oscillator.Construction.LocalCover k N ψ) (ha : Oscillator.Construction.localProjection k N ψ a = Local.Generators.Construction.weylSymplectic k N)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure]
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace k N → k) (hq : Continuous q) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    Integrable (fun v => ψ (q v) *
      UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val v) ν := by
  let C := ArchimedeanWeylCoefficients.LocalAnalysis.archimedeanWeylCoefficientRapid hk ψ hc hu a ha f h
  have hcont : Continuous (fun v => ψ (q v) * C v) := (hc.comp hq).mul C.continuous
  apply (C.integrable ν).norm.mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun v => by
    change ‖ψ (q v) * C v‖ ≤ ‖C v‖
    rw [norm_mul, hu, one_mul]

theorem real_weak_phase_integrable (N : ℕ) (ψ : AddChar ℝ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ N)) [ν.IsAddHaarMeasure]
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ N → ℝ) (hq : Continuous q) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) :
    Integrable (fun v => ψ (q v) *
      UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ N) f.val h.val v) ν := by
  have hk : ¬ DiscreteTopology ℝ := by
    intro hd
    let : DiscreteTopology ℝ := hd
    exact not_isOpen_singleton (0 : ℝ) (isOpen_discrete _)
  exact archimedean_weak_phase_integrable hk ψ hc hu (RealNormalization.LocalAnalysis.realRawFourierOscillator N ψ hc hu hn)
    rfl ν q hq f h

theorem complex_weak_phase_integrable (N : ℕ) (ψ : AddChar ℂ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N)) [ν.IsAddHaarMeasure]
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N → ℂ) (hq : Continuous q) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ N) :
    Integrable (fun v => ψ (q v) *
      UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure ℂ N) f.val h.val v) ν := by
  have hk : ¬ DiscreteTopology ℂ := by
    intro hd
    let : DiscreteTopology ℂ := hd
    exact not_isOpen_singleton (0 : ℂ) (isOpen_discrete _)
  exact archimedean_weak_phase_integrable hk ψ hc hu (ComplexNormalization.LocalAnalysis.complexRawFourierOscillator N ψ hc hu hn)
    rfl ν q hq f h

end Local

namespace Construction

theorem schrodingerCayleyPhase_continuous
    {k : Type} [NormedField k] [CharZero k] (N : ℕ)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) :
    Continuous (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg) := by
  have hD : Continuous (SchrodingerPairing.Construction.openCellDifference k N g hg).symm :=
    LinearMap.continuous_on_pi (SchrodingerPairing.Construction.openCellDifference k N g hg).symm.toLinearMap
  unfold SchrodingerPairing.Construction.schrodingerCayleyPhase UnitarySplitting.CayleyCompositionPhase.Construction.cayleyWeylPhase
    SchrodingerPairing.Construction.schrodingerPairing
  simp only [Matrix.toBilin'_apply]
  fun_prop

end Construction

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedWeakAnalysis
