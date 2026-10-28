import OAI.RepresentationTheory.Weil.AdelicSplitting.WeakCayleyReconstruction
import OAI.RepresentationTheory.Weil.AdelicSplitting.WeakCayleyCoefficients
import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanFourier
import OAI.RepresentationTheory.Weil.UnitarySplitting.LocalTest

/-! # Weak Cayley Bound -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.WeakCayleyBound.Construction

noncomputable section

/-! The corrected archimedean weak Cayley form has operator norm at
most one. Reconstruction and the exact coefficient energies prove the bound. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

theorem correctedWeakOpenCell_norm_bound
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
    (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (W : Oscillator.Construction.LocalCover k N ψ) (hW : Oscillator.Construction.localProjection k N ψ W = Local.Generators.Construction.weylSymplectic k N)
    (μ : Measure k) [μ.IsAddHaarMeasure]
    (hMoyal : ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
      (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val v‖ ^ 2
        ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) = Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N h)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
    (henergy : ∀ f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
      (∫ v, ‖CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => μ))
        g hg f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val‖ ^ 2
        ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) = Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N u)
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ‖CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) g hg f.val h.val‖ ≤
      ‖UnitarySplitting.Weak.Construction.testToL2 k N f‖ * ‖UnitarySplitting.Weak.Construction.testToL2 k N h‖ := by
  let ν := Measure.pi (fun _ : Fin N ⊕ Fin N => μ)
  obtain ⟨u, hu0⟩ := UnitarySplitting.LocalTest.Construction.exists_test_nonzero k hk N
  have hEu : 0 < Local.FunctionsMetaplectic.Construction.l2Energy k N u := lt_of_le_of_ne
    (integral_nonneg (fun x => sq_nonneg ‖u.val x‖))
    (Ne.symm (fun he => hu0 ((UnitarySplitting.Weak.Construction.l2Energy_eq_zero_iff k N u).mp he)))
  have hEf : 0 ≤ Local.FunctionsMetaplectic.Construction.l2Energy k N f := integral_nonneg (fun x => sq_nonneg ‖f.val x‖)
  have hEh : 0 ≤ Local.FunctionsMetaplectic.Construction.l2Energy k N h := integral_nonneg (fun x => sq_nonneg ‖h.val x‖)
  let a := UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val h.val
  let b : Local.FunctionsMetaplectic.Construction.PhaseSpace k N → ℂ := fun v => CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg
    f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val
  have ha : MemLp a 2 ν := ArchimedeanWeylAnalysis.Construction.archimedeanWeylAnalysis_memLp hk ψ hc hu W hW ν u h
  have hb : MemLp b 2 ν := WeakCayleyCoefficients.Construction.correctedWeakOpenCell_coefficient_memLp hk ψ hc hu W hW μ
    g hg f u hu0 (henergy f u)
  have hA : (∫ v, ‖a v‖ ^ 2 ∂ν) = Local.FunctionsMetaplectic.Construction.l2Energy k N u * Local.FunctionsMetaplectic.Construction.l2Energy k N h := by
    simp only [a, UnitarySplitting.WeylAnalysis.Construction.weylAnalysis, RCLike.norm_conj]
    exact hMoyal u h
  have hB : (∫ v, ‖b v‖ ^ 2 ∂ν) = Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N u := henergy f u
  have hcs := NonarchimedeanFourier.LocalAnalysis.norm_integral_conj_mul_le_energy ν a b ha hb
  rw [hA, hB] at hcs
  have hR := congrArg norm (WeakCayleyReconstruction.Construction.correctedWeakOpenCell_reconstruction hk ψ hc hu W hW ν hMoyal g hg f h u)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hEu] at hR
  have hprod : Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k N u * Local.FunctionsMetaplectic.Construction.l2Energy k N h) *
      Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N u) =
      Local.FunctionsMetaplectic.Construction.l2Energy k N u * (Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k N f) * Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k N h)) := by
    rw [Real.sqrt_mul hEu.le, Real.sqrt_mul hEf]
    calc
      _ = (Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k N u) * Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k N u)) *
          (Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k N f) * Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k N h)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hEu.le]
  rw [hprod] at hcs
  rw [UnitarySplitting.Weak.Construction.testToL2_norm, UnitarySplitting.Weak.Construction.testToL2_norm]
  apply (mul_le_mul_iff_right₀ hEu).mp
  exact hR.trans_le hcs

theorem correctedWeakOpenCell_real_norm_bound {N : ℕ}
    (hk : ¬ DiscreteTopology ℝ) (ψ : AddChar ℝ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic ℝ N) (hg : (g.val - 1).det ≠ 0) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) :
    ‖CorrectedNormalization.Construction.correctedWeakOpenCell ℝ N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ))
      g hg f.val h.val‖ ≤
      ‖UnitarySplitting.Weak.Construction.testToL2 ℝ N f‖ * ‖UnitarySplitting.Weak.Construction.testToL2 ℝ N h‖ := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ ψ
    (RealNormalization.LocalAnalysis.real_fourier_analysis N ψ hc hu hn).1
  exact correctedWeakOpenCell_norm_bound hk ψ hc hu (RealNormalization.LocalAnalysis.realRawFourierOscillator N ψ hc hu hn) rfl
    (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ) (ArchimedeanWeylEnergy.LocalAnalysis.realWeyl_energy ψ hc hu hn) g hg
    (ArchimedeanCayleyEnergy.Construction.correctedWeakOpenCell_real_coefficient_energy hk ψ hc hu hn g hg) f h

theorem correctedWeakOpenCell_complex_norm_bound {N : ℕ}
    (hk : ¬ DiscreteTopology ℂ) (ψ : AddChar ℂ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic ℂ N) (hg : (g.val - 1).det ≠ 0) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ N) :
    ‖CorrectedNormalization.Construction.correctedWeakOpenCell ℂ N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ))
      g hg f.val h.val‖ ≤
      ‖UnitarySplitting.Weak.Construction.testToL2 ℂ N f‖ * ‖UnitarySplitting.Weak.Construction.testToL2 ℂ N h‖ := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ).IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℂ ψ
    (ComplexNormalization.LocalAnalysis.complex_fourier_analysis N ψ hc hu hn).1
  exact correctedWeakOpenCell_norm_bound hk ψ hc hu (ComplexNormalization.LocalAnalysis.complexRawFourierOscillator N ψ hc hu hn) rfl
    (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ) (ArchimedeanWeylEnergy.LocalAnalysis.complexWeyl_energy ψ hc hu hn) g hg
    (ArchimedeanCayleyEnergy.Construction.correctedWeakOpenCell_complex_coefficient_energy hk ψ hc hu hn g hg) f h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.WeakCayleyBound.Construction
