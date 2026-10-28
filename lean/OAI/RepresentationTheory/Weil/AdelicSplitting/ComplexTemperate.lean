import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCharacter
import OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierCoordinates

/-! # Complex Temperate -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexTemperate.Construction

noncomputable section

/-! Polynomial growth of all derivatives of complex unitary character
phases, including the actual Cayley quadratic phase. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexNormalization.LocalAnalysis

theorem continuous_unitary_complex_character_temperate
    (ψ : AddChar ℂ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) :
    Function.HasTemperateGrowth (fun t : ℂ => ψ t) := by
  obtain ⟨b, hb⟩ := ComplexFourier.LocalAnalysis.complex_character_coefficient ψ hc hu
  have hreal := UnitarySplitting.RealCharacter.Construction.continuous_unitary_real_character_temperate
    (RealCharacters.LocalAnalysis.realCharacter 1) (by change Continuous (fun t : ℝ => (Real.fourierChar (1 * t) : ℂ)); fun_prop) (fun _ => Circle.norm_coe _)
  have hm : Function.HasTemperateGrowth (fun z : ℂ => (b * z).re) :=
    Complex.reCLM.hasTemperateGrowth.comp
      ((Function.HasTemperateGrowth.const b).mul (ContinuousLinearMap.id ℝ ℂ).hasTemperateGrowth)
  convert hreal.comp hm using 1
  exact funext hb

theorem complex_dot_temperate {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {N : ℕ}
    (f h : V → Local.FunctionsMetaplectic.Construction.Position ℂ N) (hf : Function.HasTemperateGrowth f) (hh : Function.HasTemperateGrowth h) :
    Function.HasTemperateGrowth (fun x => Local.FunctionsMetaplectic.Construction.dot (f x) (h x)) := by
  apply Function.HasTemperateGrowth.sum
  intro i _
  exact (((ContinuousLinearMap.proj i : Local.FunctionsMetaplectic.Construction.Position ℂ N →L[ℝ] ℂ).hasTemperateGrowth.comp hf).mul
    ((ContinuousLinearMap.proj i : Local.FunctionsMetaplectic.Construction.Position ℂ N →L[ℝ] ℂ).hasTemperateGrowth.comp hh))

theorem complexCayleyPhase_temperate {N : ℕ} (g : Local.FunctionsMetaplectic.Construction.Symplectic ℂ N) (hg : (g.val - 1).det ≠ 0) :
    Function.HasTemperateGrowth (SchrodingerPairing.Construction.schrodingerCayleyPhase ℂ N g hg) := by
  let D := SchrodingerPairing.Construction.openCellDifference ℂ N g hg
  have h := (UnitarySplitting.BilinearFourierCoordinates.Construction.finiteBilinearContinuous
    (UnitarySplitting.StandardTransvections.Construction.standardSymplecticBilinear ℂ N)).bilinear_hasTemperateGrowth
    (D.symm.toContinuousLinearEquiv.restrictScalars ℝ).hasTemperateGrowth
    (ContinuousLinearMap.id ℝ (Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N)).hasTemperateGrowth
  change Function.HasTemperateGrowth (fun v => SchrodingerPairing.Construction.schrodingerPairing ℂ N (D.symm v) v / 2)
  rw [CorrectedNormalization.Construction.schrodingerPairing_eq_standardBilinear]
  exact h.mul (Function.HasTemperateGrowth.const (2 : ℂ)⁻¹)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexTemperate.Construction
