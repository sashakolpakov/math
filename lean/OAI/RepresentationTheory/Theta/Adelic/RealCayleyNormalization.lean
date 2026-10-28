import OAI.RepresentationTheory.Weil.AdelicSplitting.RealWeakUnitary
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalizationAnalysis
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCanonicalCayley

/-! # Real Cayley Normalization -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealCayleyNormalization

noncomputable section

/-! UnitarySplitting's constructed positive real Cayley lift has exactly the corrected
AdelicSplitting weak normalization. No equality of normalized operators is assumed. -/

open _root_.MeasureTheory
open scoped ComplexConjugate InnerProductSpace

variable {E : Type} [NormedField E] [Algebra ℝ E] {m n : ℕ}
variable (σ : E ≃ₐ[ℝ] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K)
variable (ψ : AddChar ℝ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
variable (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℝ (m * n)) (hg : (g.val - 1).det ≠ 0)

theorem real_cayley_radius_and_pairing :
    let ν := Measure.pi (fun _ : Fin (m * n) ⊕ Fin (m * n) => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ)
    letI : ν.IsAddHaarMeasure := by
      let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).IsAddHaarMeasure :=
        Weil.AdelicSplitting.FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ ψ (Weil.AdelicSplitting.RealNormalization.LocalAnalysis.real_fourier_analysis (m * n) ψ hc hu hn).1
      infer_instance
    let A := Weil.UnitarySplitting.RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν
      (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix ℝ (m * n) g) (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference ℝ (m * n) g hg)
      (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply ℝ (m * n) g hg)
    Weil.UnitarySplitting.RealCayleyLift.Construction.realCayleyLiftRadius σ H K c ψ hc hu hn ν
      (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix ℝ (m * n) g) (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference ℝ (m * n) g hg)
      (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply ℝ (m * n) g hg) = Weil.AdelicSplitting.Normalization.Construction.openCellScale ℝ (m * n) g ∧
      ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ (m * n),
        (∫ x, (A.val.2 f).val x * conj (h.val x) ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ (m * n)) =
          Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue ℝ (m * n) ψ g f.val h.val := by
  dsimp only
  let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).IsAddHaarMeasure :=
    Weil.AdelicSplitting.FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ ψ (Weil.AdelicSplitting.RealNormalization.LocalAnalysis.real_fourier_analysis (m * n) ψ hc hu hn).1
  let ν := Measure.pi (fun _ : Fin (m * n) ⊕ Fin (m * n) => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ)
  let M := Weil.UnitarySplitting.RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν
    (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix ℝ (m * n) g) (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference ℝ (m * n) g hg)
    (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply ℝ (m * n) g hg)
  let A := Weil.UnitarySplitting.RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν
    (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix ℝ (m * n) g) (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference ℝ (m * n) g hg)
    (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply ℝ (m * n) g hg)
  obtain ⟨hr, _, hM⟩ := Weil.UnitarySplitting.RealCayleyLift.Construction.realCayleyLift_spec σ H K c ψ hc hu hn ν
    (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix ℝ (m * n) g) (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference ℝ (m * n) g hg)
    (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply ℝ (m * n) g hg)
  obtain ⟨U, _, hU⟩ := Weil.AdelicSplitting.RealWeakUnitary.Construction.correctedWeakOpenCell_real_unitary Weil.UnitarySplitting.RealFourierUnitary.Construction.real_nondiscrete ψ hc hu hn g hg
  have hs : 0 < Weil.AdelicSplitting.Normalization.Construction.openCellScale ℝ (m * n) g := by
    rw [Weil.AdelicSplitting.Normalization.Construction.openCellScale, dite_eq_left hg]
    exact Real.sqrt_pos.mpr (Weil.Local.FunctionsMetaplectic.Construction.localModulus_pos ℝ _)
  have hMU (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ (m * n)) : M f = (Weil.AdelicSplitting.Normalization.Construction.openCellScale ℝ (m * n) g : ℂ) • U.val.2 f := by
    have he : Weil.AdelicSplitting.RealWeakUnitary.Construction.correctedRealCayleyTestOperator ψ hc hu hn ν g hg f = U.val.2 f := by
      apply Weil.AdelicSplitting.CorrectedNormalizationAnalysis.Construction.integral_test_pairing_ext
      intro h
      rw [← Weil.UnitarySplitting.Weak.Construction.testToL2_inner, Weil.AdelicSplitting.RealWeakUnitary.Construction.correctedRealCayleyTestOperator_pairing]
      exact hU f h
    have ht := congrArg (fun v : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ (m * n) =>
      (Weil.AdelicSplitting.Normalization.Construction.openCellScale ℝ (m * n) g : ℂ) • v) he
    change (Weil.AdelicSplitting.Normalization.Construction.openCellScale ℝ (m * n) g : ℂ) • ((Weil.AdelicSplitting.Normalization.Construction.openCellScale ℝ (m * n) g : ℂ)⁻¹ • M f) = _ at ht
    rwa [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs.ne'), one_smul] at ht
  obtain ⟨f₀, hf₀⟩ := Weil.UnitarySplitting.LocalTest.Construction.exists_test_nonzero ℝ Weil.UnitarySplitting.RealFourierUnitary.Construction.real_nondiscrete (m * n)
  obtain ⟨hradius, hoperator⟩ := Weil.UnitarySplitting.PositiveCommutation.Construction.positive_operator_normalization_unique M A.val.2 U.val.2
    A.property.1 U.property.1 f₀ hf₀ _ _ hr hs hM hMU
  refine ⟨hradius, fun f h => ?_⟩
  change (∫ x, (A.val.2 f).val x * conj (h.val x) ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ (m * n)) = _
  rw [hoperator, Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue_open ℝ (m * n) ψ g hg]
  exact (hU f h).symm

end

end OAI.RepresentationTheory.Theta.Adelic.RealCayleyNormalization
