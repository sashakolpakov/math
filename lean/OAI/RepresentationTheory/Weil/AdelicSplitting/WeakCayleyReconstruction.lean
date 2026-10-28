import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylResolution
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeakSynthesis
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianLinearity

/-! # Weak Cayley Reconstruction -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! Reconstruction expresses the corrected weak Cayley form as an
ordinary L² pairing of its coherent coefficients and Weyl analysis. -/

section

open scoped ComplexConjugate

def RapidFunctions.LocalAnalysis.RapidFunction.conjugate {V : Type*} [NormedAddCommGroup V]
    (f : RapidFunctions.LocalAnalysis.RapidFunction V) : RapidFunctions.LocalAnalysis.RapidFunction V where
  toContinuousMap := ⟨fun x => conj (f x), f.continuous.star⟩
  decay j := by
    obtain ⟨C, hC, hb⟩ := f.decay j
    refine ⟨C, hC, fun x => ?_⟩
    change (1 + ‖x‖) ^ j * ‖conj (f x)‖ ≤ C
    simpa only [RCLike.norm_conj] using hb x

end

namespace WeakCayleyReconstruction.Construction

open _root_.MeasureTheory
open scoped ComplexConjugate

theorem correctedWeakOpenCell_reconstruction
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
    (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (W : Oscillator.Construction.LocalCover k N ψ) (hW : Oscillator.Construction.localProjection k N ψ W = Local.Generators.Construction.weylSymplectic k N)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure]
    (hMoyal : ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
      (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val v‖ ^ 2 ∂ν) =
        Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N h)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) (f h u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (Local.FunctionsMetaplectic.Construction.l2Energy k N u : ℂ) * CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val h.val =
      ∫ v, conj (UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val h.val v) *
        CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val ∂ν := by
  let a := (ArchimedeanWeylCoefficients.LocalAnalysis.archimedeanWeylCoefficientRapid hk ψ hc hu W hW u h).conjugate
  have ha (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) : a v = UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val h.val v := rfl
  have hres : ((Local.FunctionsMetaplectic.Construction.l2Energy k N u : ℂ) • h).val = UnitarySplitting.WeylSynthesisAdd.Construction.weylSynthesis ψ ν a u.val := by
    exact (ArchimedeanWeylResolution.Construction.archimedeanWeylResolution hk ψ hc hu W hW ν u hMoyal h).symm
  have hp := ArchimedeanWeakSynthesis.Construction.archimedeanWeakGaussian_synthesized_output hk ψ hc hu W hW ν
    (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg) (CorrectedWeakAnalysis.Construction.schrodingerCayleyPhase_continuous N g hg)
    a f u ((Local.FunctionsMetaplectic.Construction.l2Energy k N u : ℂ) • h) hres
  rw [UnitarySplitting.WeakGaussianLinearity.Construction.weakWeylGaussian_smul_right hk ψ hc hu, Complex.conj_ofReal] at hp
  simp_rw [ha] at hp
  unfold CorrectedNormalization.Construction.correctedWeakOpenCell
  calc
    _ = (Normalization.Construction.openCellScale k N g : ℂ)⁻¹ * ((Local.FunctionsMetaplectic.Construction.l2Energy k N u : ℂ) *
        UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) ν
          (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg) f.val h.val) := by ring
    _ = (Normalization.Construction.openCellScale k N g : ℂ)⁻¹ * ∫ v,
        conj (UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val h.val v) *
          UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) ν (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg)
            f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val ∂ν := by rw [hp]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by dsimp only; ring

end WeakCayleyReconstruction.Construction

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
