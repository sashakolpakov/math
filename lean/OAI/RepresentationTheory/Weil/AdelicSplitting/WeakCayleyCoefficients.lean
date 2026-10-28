import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCayleyEnergy
import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak

/-! # Weak Cayley Coefficients -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.WeakCayleyCoefficients.Construction

noncomputable section

/-! Explicit continuous coherent coefficients for the corrected weak
Cayley form, together with their square integrability. -/

open _root_.MeasureTheory
open OAI.RepresentationTheory.Weil.UnitarySplitting.Weak.Construction

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
variable (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)

theorem correctedWeakOpenCell_coefficient_formula
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure]
    (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val =
      (Normalization.Construction.openCellScale k N g : ℂ)⁻¹ * (ψ (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg v) *
        ∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing k N ((SchrodingerPairing.Construction.openCellDifference k N g hg).symm v) w) *
          (ψ (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg w) *
            UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val u.val w) ∂ν) := by
  unfold CorrectedNormalization.Construction.correctedWeakOpenCell SchrodingerPairing.Construction.schrodingerCayleyPhase
  rw [CorrectedNormalization.Construction.schrodingerPairing_eq_standardBilinear]
  rw [UnitarySplitting.WeakCayleyCoefficients.Construction.weakCayleyGaussian_output_coefficient hk ψ hc hu ν
    (CorrectedNormalization.Construction.standardSymplecticOfMatrix k N g) (SchrodingerPairing.Construction.openCellDifference k N g hg) (SchrodingerPairing.Construction.openCellDifference_apply k N g hg)]

omit [CompleteSpace k] [CharZero k] [SecondCountableTopology k] in
theorem correctedWeakOpenCell_zero_left
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
    (h : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) : CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg 0 h = 0 := by
  simp [CorrectedNormalization.Construction.correctedWeakOpenCell, UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian, UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient, Local.FunctionsMetaplectic.Construction.heisenbergFunction]

variable [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
variable (W : Oscillator.Construction.LocalCover k N ψ) (hW : Oscillator.Construction.localProjection k N ψ W = Local.Generators.Construction.weylSymplectic k N)
variable (μ : Measure k) [μ.IsAddHaarMeasure]

include W hW in
theorem correctedWeakOpenCell_coefficient_continuous
    (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    Continuous (fun v => CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => μ))
      g hg f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val) := by
  let φ : Local.FunctionsMetaplectic.Construction.PhaseSpace k N → ℂ := fun w => ψ (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg w) *
    UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val u.val w
  have hi : Integrable φ (Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) :=
    CorrectedWeakAnalysis.Local.archimedean_weak_phase_integrable hk ψ hc hu W hW _
      (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg) (CorrectedWeakAnalysis.Construction.schrodingerCayleyPhase_continuous N g hg) f u
  have hT := PhaseFourier.Construction.phaseFourier_continuous k N ψ hu hc μ φ hi
  have hD : Continuous (SchrodingerPairing.Construction.openCellDifference k N g hg).symm :=
    LinearMap.continuous_on_pi (SchrodingerPairing.Construction.openCellDifference k N g hg).symm.toLinearMap
  simp_rw [correctedWeakOpenCell_coefficient_formula]
  exact continuous_const.mul ((hc.comp (CorrectedWeakAnalysis.Construction.schrodingerCayleyPhase_continuous N g hg)).mul (hT.comp hD))

include W hW in
theorem correctedWeakOpenCell_coefficient_memLp
    (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (hu0 : u ≠ 0)
    (henergy : (∫ v, ‖CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => μ))
      g hg f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val‖ ^ 2
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) = Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N u) :
    MemLp (fun v => CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => μ))
      g hg f.val (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u).val) 2 (Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) := by
  by_cases hf0 : f = 0
  · subst f
    simp only [Submodule.coe_zero, correctedWeakOpenCell_zero_left]
    exact MemLp.zero
  · have hfn : Local.FunctionsMetaplectic.Construction.l2Energy k N f ≠ 0 := fun he =>
      hf0 ((UnitarySplitting.Weak.Construction.l2Energy_eq_zero_iff k N f).mp he)
    have hun : Local.FunctionsMetaplectic.Construction.l2Energy k N u ≠ 0 := fun he =>
      hu0 ((UnitarySplitting.Weak.Construction.l2Energy_eq_zero_iff k N u).mp he)
    apply (memLp_two_iff_integrable_sq_norm
      (correctedWeakOpenCell_coefficient_continuous hk ψ hc hu W hW μ g hg f u).aestronglyMeasurable).mpr
    apply Integrable.of_integral_ne_zero
    rw [henergy]
    exact mul_ne_zero hfn hun

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.WeakCayleyCoefficients.Construction
