import OAI.RepresentationTheory.Weil.AdelicSplitting.UltraWeakUnitary
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalizationAnalysis
import OAI.RepresentationTheory.Weil.UnitarySplitting.CanonicalCayleyLift

/-! # Ultra Cayley Normalization -/

namespace OAI.RepresentationTheory.Theta.Adelic.UltraCayleyNormalization

noncomputable section

/-! UnitarySplitting's constructed positive nonarchimedean Cayley lift has exactly the corrected
AdelicSplitting weak normalization. No equality of normalized operators is assumed. -/

open _root_.MeasureTheory
open scoped ComplexConjugate InnerProductSpace

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
variable [IsUltrametricDist k] [ProperSpace k] [NonarchimedeanAddGroup k]
variable {E : Type} [NormedField E] [Algebra k E] {m n : ℕ}
variable (σ : E ≃ₐ[k] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K)
variable (hk : ¬ DiscreteTopology k)
variable (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
variable (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k (m * n)) (hg : (g.val - 1).det ≠ 0)

theorem ultra_cayley_radius_and_pairing :
    let ν := Measure.pi (fun _ : Fin (m * n) ⊕ Fin (m * n) => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ)
    letI : ν.IsAddHaarMeasure := by
      let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
        Weil.AdelicSplitting.FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos k ψ (Weil.AdelicSplitting.NonarchimedeanReference.LocalAnalysis.nonarchimedean_one_coordinate_normalization ψ hu hc hn).1
      infer_instance
    let A := Weil.UnitarySplitting.CanonicalCayleyLift.Construction.ultraCayleyLift σ H K c hk ψ hc hu hn ν
      (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix k (m * n) g) (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k (m * n) g hg)
      (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply k (m * n) g hg)
    Weil.UnitarySplitting.CanonicalCayleyLift.Construction.ultraCayleyLiftRadius σ H K c hk ψ hc hu hn ν
      (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix k (m * n) g) (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k (m * n) g hg)
      (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply k (m * n) g hg) = Weil.AdelicSplitting.Normalization.Construction.openCellScale k (m * n) g ∧
      ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (m * n),
        (∫ x, (A.val.2 f).val x * conj (h.val x) ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (m * n)) =
          Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k (m * n) ψ g f.val h.val := by
  dsimp only
  let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
    Weil.AdelicSplitting.FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos k ψ (Weil.AdelicSplitting.NonarchimedeanReference.LocalAnalysis.nonarchimedean_one_coordinate_normalization ψ hu hc hn).1
  let ν := Measure.pi (fun _ : Fin (m * n) ⊕ Fin (m * n) => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ)
  let M := Weil.UnitarySplitting.UltraCayleyOperator.Construction.ultraCayleyOperator hk ψ hc hu hn ν
    (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix k (m * n) g) (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k (m * n) g hg)
    (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply k (m * n) g hg)
  let A := Weil.UnitarySplitting.CanonicalCayleyLift.Construction.ultraCayleyLift σ H K c hk ψ hc hu hn ν
    (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix k (m * n) g) (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k (m * n) g hg)
    (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply k (m * n) g hg)
  obtain ⟨hr, _, hM⟩ := Weil.UnitarySplitting.CanonicalCayleyLift.Construction.ultraCayleyLift_spec σ H K c hk ψ hc hu hn ν
    (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix k (m * n) g) (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k (m * n) g hg)
    (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply k (m * n) g hg)
  obtain ⟨U, _, hU⟩ := Weil.AdelicSplitting.UltraWeakUnitary.Construction.correctedWeakOpenCell_ultra_unitary hk ψ hc hu hn g hg
  have hs : 0 < Weil.AdelicSplitting.Normalization.Construction.openCellScale k (m * n) g := by
    rw [Weil.AdelicSplitting.Normalization.Construction.openCellScale, dite_eq_left hg]
    exact Real.sqrt_pos.mpr (Weil.Local.FunctionsMetaplectic.Construction.localModulus_pos k _)
  have hMU (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (m * n)) : M f = (Weil.AdelicSplitting.Normalization.Construction.openCellScale k (m * n) g : ℂ) • U.val.2 f := by
    have he : (Weil.AdelicSplitting.Normalization.Construction.openCellScale k (m * n) g : ℂ)⁻¹ • M f = U.val.2 f := by
      apply Weil.AdelicSplitting.CorrectedNormalizationAnalysis.Construction.integral_test_pairing_ext
      intro h
      rw [← Weil.UnitarySplitting.Weak.Construction.testToL2_inner, map_smul, inner_smul_right]
      have hraw := Weil.UnitarySplitting.UltraCayleyOperator.Construction.ultraCayleyOperator_pairing hk ψ hc hu hn ν
        (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix k (m * n) g) (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k (m * n) g hg)
        (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply k (m * n) g hg) f h
      change ⟪Weil.UnitarySplitting.Weak.Construction.testToL2 k (m * n) h, Weil.UnitarySplitting.Weak.Construction.testToL2 k (m * n) (M f)⟫_ℂ = _ at hraw
      rw [hraw]
      have hnorm := hU f h
      unfold Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCell Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase at hnorm
      rw [Weil.AdelicSplitting.CorrectedNormalization.Construction.schrodingerPairing_eq_standardBilinear] at hnorm
      exact hnorm
    have ht := congrArg (fun v : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (m * n) =>
      (Weil.AdelicSplitting.Normalization.Construction.openCellScale k (m * n) g : ℂ) • v) he
    change (Weil.AdelicSplitting.Normalization.Construction.openCellScale k (m * n) g : ℂ) • ((Weil.AdelicSplitting.Normalization.Construction.openCellScale k (m * n) g : ℂ)⁻¹ • M f) = _ at ht
    rwa [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs.ne'), one_smul] at ht
  obtain ⟨f₀, hf₀⟩ := Weil.UnitarySplitting.LocalTest.Construction.exists_test_nonzero k hk (m * n)
  obtain ⟨hradius, hoperator⟩ := Weil.UnitarySplitting.PositiveCommutation.Construction.positive_operator_normalization_unique M A.val.2 U.val.2
    A.property.1 U.property.1 f₀ hf₀ _ _ hr hs hM hMU
  refine ⟨hradius, fun f h => ?_⟩
  change (∫ x, (A.val.2 f).val x * conj (h.val x) ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (m * n)) = _
  rw [hoperator, Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue_open k (m * n) ψ g hg]
  exact (hU f h).symm

end

end OAI.RepresentationTheory.Theta.Adelic.UltraCayleyNormalization
