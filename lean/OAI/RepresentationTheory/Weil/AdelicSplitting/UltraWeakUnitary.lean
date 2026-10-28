import OAI.RepresentationTheory.Weil.AdelicSplitting.UltraCayleyEnergy
import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalSurjectivity
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraIntertwinerNormalization

/-! # Ultra Weak Unitary -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.UltraWeakUnitary.Construction

noncomputable section

/-! Actual unitary realization of the corrected weak open-cell integral
at every nonarchimedean local field. Its radius is the prescribed square
root of the determinant modulus, proved from the integral's energy. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.UltraIntertwinerNormalization.Construction _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate NNReal

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
variable [IsUltrametricDist k] [ProperSpace k] [NonarchimedeanAddGroup k] {N : ℕ}

theorem correctedWeakOpenCell_ultra_unitary
    (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
    (hc : Continuous (fun t : k => ψ t)) (hu : ∀ t : k, ‖ψ t‖ = 1) (hn : ∃ t : k, ψ t ≠ 1)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) :
    ∃ U : Oscillator.Construction.LocalCover k N ψ, Oscillator.Construction.localProjection k N ψ U = g ∧
      ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
        CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ))
          g hg f.val h.val =
        ∫ x, (Oscillator.Construction.localOperator k N ψ U f).val x * conj (h.val x) ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure k N := by
  let μ := Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ
  let : μ.IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos k ψ
    (NonarchimedeanReference.LocalAnalysis.nonarchimedean_one_coordinate_normalization ψ hu hc hn).1
  let : (Local.FunctionsMetaplectic.Construction.positionMeasure k (N + N) ψ).IsAddHaarMeasure := by
    change (Measure.pi (fun _ : Fin (N + N) => μ)).IsAddHaarMeasure
    infer_instance
  let ν := Measure.pi (fun _ : Fin N ⊕ Fin N => μ)
  let M := UltraCayleyEnergy.Construction.matrixUltraCayleyOperator hk ψ hc hu hn μ g hg
  have hM0 : M ≠ 0 := UnitarySplitting.UltraCayleyOperator.Construction.ultraCayleyOperator_ne_zero hk ψ hc hu hn ν
    (CorrectedNormalization.Construction.standardSymplecticOfMatrix k N g) (SchrodingerPairing.Construction.openCellDifference k N g hg) (SchrodingerPairing.Construction.openCellDifference_apply k N g hg)
  have hMcov (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
      M (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f) =
        UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu (Local.FunctionsMetaplectic.Construction.symplecticAction g v) (M f) :=
    UnitarySplitting.UltraCayleyOperator.Construction.ultraCayleyOperator_intertwines hk ψ hc hu hn ν
      (CorrectedNormalization.Construction.standardSymplecticOfMatrix k N g) (SchrodingerPairing.Construction.openCellDifference k N g hg) (SchrodingerPairing.Construction.openCellDifference_apply k N g hg) v f
  obtain ⟨a, ha⟩ := LocalSurjectivity.Construction.localProjection_surjective_ultra ψ hu hc hn g
  have hacov (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
      a.val.2 (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f) =
        UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu (Local.FunctionsMetaplectic.Construction.symplecticAction g v) (a.val.2 f) := by
    apply Subtype.ext
    have hh := (a.property.2 v f (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f)).mp rfl
    change (a.val.2 (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f)).val =
      Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Local.FunctionsMetaplectic.Construction.symplecticAction (Oscillator.Construction.localProjection k N ψ a) v) (a.val.2 f).val at hh
    rwa [ha] at hh
  obtain ⟨r, V, hr, hM, henergy, hcov⟩ := UnitarySplitting.UltraIntertwinerNormalization.Construction.ultraIntertwiner_positive_normalization hk ψ hc hu hn
    (Local.FunctionsMetaplectic.Construction.symplecticAction g) M hM0 hMcov a.val.2 hacov a.property.1
  have hscale : Normalization.Construction.openCellScale k N g = Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k (g.val - 1).det : ℝ) := by
    rw [Normalization.Construction.openCellScale, dite_eq_left hg]
    congr 1
    exact congrArg (fun z : ℝ≥0 => (z : ℝ))
      (DeterminantMeasure.LocalAnalysis.haarModulus_unit k (Units.mk0 (g.val - 1).det hg)).symm
  obtain ⟨u, hu0⟩ := UnitarySplitting.LocalTest.Construction.exists_test_nonzero k hk N
  have huE : Local.FunctionsMetaplectic.Construction.l2Energy k N u ≠ 0 := by
    intro hz
    exact hu0 ((UnitarySplitting.Weak.Construction.l2Energy_eq_zero_iff k N u).mp hz)
  have hME := UltraCayleyEnergy.Construction.matrixUltraCayley_energy hk ψ hc hu hn μ
    (NonarchimedeanIntertwiner.LocalAnalysis.nonarchimedean_fourier_mem ψ hu hc hn (Local.FunctionsMetaplectic.Construction.positionMeasure k (N + N) ψ))
    (NonarchimedeanNormalization.LocalAnalysis.nonarchimedean_fourier_inversion ψ hu hc hn (N + N)) g hg u
  change Local.FunctionsMetaplectic.Construction.l2Energy k N (M u) = _ at hME
  rw [hM, UnitarySplitting.FourierPairing.Construction.l2Energy_smul, henergy, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hME
  have hr2 : r ^ 2 = (DeterminantMeasure.LocalAnalysis.haarModulus k (g.val - 1).det : ℝ) := mul_right_cancel₀ huE hME
  have hrs : r = Normalization.Construction.openCellScale k N g := by
    rw [hscale, ← hr2, Real.sqrt_sq hr.le]
  let U : Oscillator.Construction.LocalCover k N ψ := ⟨(g, V), ⟨henergy, by
    intro v f h
    constructor
    · intro hh
      have hh' : h = UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f := Subtype.ext hh
      rw [hh']
      exact congrArg Subtype.val (hcov v f)
    · intro hh
      have hh' : V h = UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu (Local.FunctionsMetaplectic.Construction.symplecticAction g v) (V f) := Subtype.ext hh
      rw [← hcov] at hh'
      exact congrArg Subtype.val (V.injective hh')⟩⟩
  refine ⟨U, rfl, fun f h => ?_⟩
  have hp := UnitarySplitting.UltraCayleyOperator.Construction.ultraCayleyOperator_pairing hk ψ hc hu hn ν
    (CorrectedNormalization.Construction.standardSymplecticOfMatrix k N g) (SchrodingerPairing.Construction.openCellDifference k N g hg)
    (SchrodingerPairing.Construction.openCellDifference_apply k N g hg) f h
  change ⟪UnitarySplitting.Weak.Construction.testToL2 k N h, UnitarySplitting.Weak.Construction.testToL2 k N (M f)⟫_ℂ = _ at hp
  rw [hM, map_smul, inner_smul_right] at hp
  unfold CorrectedNormalization.Construction.correctedWeakOpenCell SchrodingerPairing.Construction.schrodingerCayleyPhase
  rw [CorrectedNormalization.Construction.schrodingerPairing_eq_standardBilinear, ← hp, ← hrs, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), one_mul, UnitarySplitting.Weak.Construction.testToL2_inner]
  rfl

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.UltraWeakUnitary.Construction
