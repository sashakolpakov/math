import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCayley
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylHilbert

/-! # Archimedean Cayley Isometry -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCayleyIsometry.Construction

noncomputable section

section

/-! Exact norm preservation of the Hilbert-space operator representing
the corrected Cayley integral, derived from its coefficient energy. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
variable (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure]
variable (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
variable (W : Oscillator.Construction.LocalCover k N ψ) (hW : Oscillator.Construction.localProjection k N ψ W = Local.Generators.Construction.weylSymplectic k N)
variable (hbound : ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
  ‖CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val h.val‖ ≤
    ‖UnitarySplitting.Weak.Construction.testToL2 k N f‖ * ‖UnitarySplitting.Weak.Construction.testToL2 k N h‖)
variable (hMoyal : ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
  (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val v‖ ^ 2 ∂ν) =
    Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N h)
variable (henergy : ∀ f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
  (∫ v, ‖CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val
    (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val‖ ^ 2 ∂ν) = Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N u)

include hMoyal henergy

theorem correctedCayleyHilbertVector_norm_exact (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ‖ArchimedeanCayley.Construction.correctedCayleyHilbertVector hk ψ hc hu ν g hg W hW hbound f‖ =
      ‖UnitarySplitting.Weak.Construction.testToL2 k N f‖ := by
  obtain ⟨u, hu0⟩ := UnitarySplitting.LocalTest.Construction.exists_test_nonzero k hk N
  have hEu : Local.FunctionsMetaplectic.Construction.l2Energy k N u ≠ 0 := fun he =>
    hu0 ((UnitarySplitting.Weak.Construction.l2Energy_eq_zero_iff k N u).mp he)
  have he := ArchimedeanWeylHilbert.Construction.archimedeanWeylHilbert_coefficient_energy hk ψ hc hu W hW ν u hMoyal
    (ArchimedeanCayley.Construction.correctedCayleyHilbertVector hk ψ hc hu ν g hg W hW hbound f)
  simp only [ArchimedeanCayley.Construction.correctedCayleyHilbertVector_pairing] at he
  rw [henergy] at he
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [UnitarySplitting.Weak.Construction.testToL2_norm,
    Real.sq_sqrt (show 0 ≤ Local.FunctionsMetaplectic.Construction.l2Energy k N f from integral_nonneg (fun x => sq_nonneg ‖f.val x‖))]
  apply mul_left_cancel₀ hEu
  exact he.symm.trans (mul_comm _ _)

theorem correctedCayleyHilbertOperator_norm_exact (x : Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)) :
    ‖ArchimedeanCayley.Construction.correctedCayleyHilbertOperator hk ψ hc hu ν g hg W hW hbound x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hb (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
      ‖ArchimedeanCayley.Construction.correctedCayleyHilbertTestOperator hk ψ hc hu ν g hg W hW hbound f‖ ≤
        1 * ‖UnitarySplitting.Weak.Construction.testToL2 k N f‖ := by
    simpa only [one_mul] using! ArchimedeanCayley.Construction.correctedCayleyHilbertVector_norm hk ψ hc hu ν g hg W hW hbound f
  have hn (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
      ‖ArchimedeanCayley.Construction.correctedCayleyHilbertTestOperator hk ψ hc hu ν g hg W hW hbound f‖ ^ 2 =
        1 * ‖UnitarySplitting.Weak.Construction.testToL2 k N f‖ ^ 2 := by
    simpa only [one_mul] using! congrArg (fun r : ℝ => r ^ 2)
      (correctedCayleyHilbertVector_norm_exact hk ψ hc hu ν g hg W hW hbound hMoyal henergy f)
  simpa only [one_mul] using! DenseExtension.Construction.dense_linear_extension_norm_sq
    (UnitarySplitting.Weak.Construction.testToL2 k N) (ArchimedeanSpace.Construction.archimedean_testToL2_dense N) _ 1 1 hb hn x

theorem correctedCayleyHilbertOperator_isometry :
    Isometry (ArchimedeanCayley.Construction.correctedCayleyHilbertOperator hk ψ hc hu ν g hg W hW hbound) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact correctedCayleyHilbertOperator_norm_exact hk ψ hc hu ν g hg W hW hbound hMoyal henergy (x - y)

end

/-! The corrected real and complex weak Cayley integrals are represented
by actual Hilbert-space isometries. All analytic hypotheses are discharged
by the independently proved Fourier and coefficient-energy identities. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

theorem correctedWeakOpenCell_real_hilbert_isometry {N : ℕ}
    (hk : ¬ DiscreteTopology ℝ) (ψ : AddChar ℝ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic ℝ N) (hg : (g.val - 1).det ≠ 0) :
    ∃ M : Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ N) →L[ℂ] Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ N),
      Isometry M ∧ ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N,
        ⟪UnitarySplitting.Weak.Construction.testToL2 ℝ N h, M (UnitarySplitting.Weak.Construction.testToL2 ℝ N f)⟫_ℂ =
          CorrectedNormalization.Construction.correctedWeakOpenCell ℝ N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ))
            g hg f.val h.val := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ ψ
    (RealNormalization.LocalAnalysis.real_fourier_analysis N ψ hc hu hn).1
  let ν := Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ)
  let W := RealNormalization.LocalAnalysis.realRawFourierOscillator N ψ hc hu hn
  have hW : Oscillator.Construction.localProjection ℝ N ψ W = Local.Generators.Construction.weylSymplectic ℝ N := rfl
  have hb := WeakCayleyBound.Construction.correctedWeakOpenCell_real_norm_bound hk ψ hc hu hn g hg
  refine ⟨ArchimedeanCayley.Construction.correctedCayleyHilbertOperator hk ψ hc hu ν g hg W hW hb, ?_, ?_⟩
  · exact correctedCayleyHilbertOperator_isometry hk ψ hc hu ν g hg W hW hb
      (ArchimedeanWeylEnergy.LocalAnalysis.realWeyl_energy ψ hc hu hn) (ArchimedeanCayleyEnergy.Construction.correctedWeakOpenCell_real_coefficient_energy hk ψ hc hu hn g hg)
  · exact ArchimedeanCayley.Construction.correctedCayleyHilbertOperator_pairing hk ψ hc hu ν g hg W hW hb

theorem correctedWeakOpenCell_complex_hilbert_isometry {N : ℕ}
    (hk : ¬ DiscreteTopology ℂ) (ψ : AddChar ℂ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic ℂ N) (hg : (g.val - 1).det ≠ 0) :
    ∃ M : Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure ℂ N) →L[ℂ] Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure ℂ N),
      Isometry M ∧ ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ N,
        ⟪UnitarySplitting.Weak.Construction.testToL2 ℂ N h, M (UnitarySplitting.Weak.Construction.testToL2 ℂ N f)⟫_ℂ =
          CorrectedNormalization.Construction.correctedWeakOpenCell ℂ N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ))
            g hg f.val h.val := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ).IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℂ ψ
    (ComplexNormalization.LocalAnalysis.complex_fourier_analysis N ψ hc hu hn).1
  let ν := Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ)
  let W := ComplexNormalization.LocalAnalysis.complexRawFourierOscillator N ψ hc hu hn
  have hW : Oscillator.Construction.localProjection ℂ N ψ W = Local.Generators.Construction.weylSymplectic ℂ N := rfl
  have hb := WeakCayleyBound.Construction.correctedWeakOpenCell_complex_norm_bound hk ψ hc hu hn g hg
  refine ⟨ArchimedeanCayley.Construction.correctedCayleyHilbertOperator hk ψ hc hu ν g hg W hW hb, ?_, ?_⟩
  · exact correctedCayleyHilbertOperator_isometry hk ψ hc hu ν g hg W hW hb
      (ArchimedeanWeylEnergy.LocalAnalysis.complexWeyl_energy ψ hc hu hn) (ArchimedeanCayleyEnergy.Construction.correctedWeakOpenCell_complex_coefficient_energy hk ψ hc hu hn g hg)
  · exact ArchimedeanCayley.Construction.correctedCayleyHilbertOperator_pairing hk ψ hc hu ν g hg W hW hb

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCayleyIsometry.Construction
