import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedWeakAnalysis
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianLinearity

/-! # Archimedean Weak Linearity -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeakLinearity.Construction

noncomputable section

/-! Sesquilinearity of the actual corrected archimedean weak integral,
with additivity justified by its proved absolute convergence. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedWeakAnalysis.Local _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
variable (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)

include hk hc hu in
theorem weylMatrixCoefficient_add_left (f₁ f₂ h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) (f₁ + f₂).val h.val v =
      UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f₁.val h.val v +
        UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f₂.val h.val v := by
  rw [UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hk ψ hc hu, map_add, map_add, inner_add_right,
    ← UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hk ψ hc hu, ← UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hk ψ hc hu]

include hk hc hu in
theorem weylMatrixCoefficient_add_right (f h₁ h₂ : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val (h₁ + h₂).val v =
      UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h₁.val v +
        UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h₂.val v := by
  rw [UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hk ψ hc hu, map_add, inner_add_left,
    ← UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hk ψ hc hu, ← UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hk ψ hc hu]

variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N))
variable (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)

include hk hc hu in
theorem correctedWeakOpenCell_smul_left (z : ℂ) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg (z • f).val h.val =
      z * CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val h.val := by
  unfold CorrectedNormalization.Construction.correctedWeakOpenCell
  rw [UnitarySplitting.WeakGaussianLinearity.Construction.weakWeylGaussian_smul_left hk ψ hc hu]
  ring

include hk hc hu in
theorem correctedWeakOpenCell_smul_right (z : ℂ) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val (z • h).val =
      conj z * CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val h.val := by
  unfold CorrectedNormalization.Construction.correctedWeakOpenCell
  rw [UnitarySplitting.WeakGaussianLinearity.Construction.weakWeylGaussian_smul_right hk ψ hc hu]
  ring

variable [NormedAlgebra ℝ k] [FiniteDimensional ℝ k] [ν.IsAddHaarMeasure]
variable (W : Oscillator.Construction.LocalCover k N ψ) (hW : Oscillator.Construction.localProjection k N ψ W = Local.Generators.Construction.weylSymplectic k N)

include hk hc hu W hW in
theorem correctedWeakOpenCell_add_left (f₁ f₂ h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg (f₁ + f₂).val h.val =
      CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f₁.val h.val +
        CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f₂.val h.val := by
  have hI (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) := CorrectedWeakAnalysis.Local.archimedean_weak_phase_integrable hk ψ hc hu W hW ν
    (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg) (CorrectedWeakAnalysis.Construction.schrodingerCayleyPhase_continuous N g hg) f h
  unfold CorrectedNormalization.Construction.correctedWeakOpenCell UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian
  simp_rw [weylMatrixCoefficient_add_left hk ψ hc hu, mul_add]
  rw [integral_add (hI f₁) (hI f₂), mul_add]

include hk hc hu W hW in
theorem correctedWeakOpenCell_add_right (f h₁ h₂ : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val (h₁ + h₂).val =
      CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val h₁.val +
        CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val h₂.val := by
  have hI (h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) := CorrectedWeakAnalysis.Local.archimedean_weak_phase_integrable hk ψ hc hu W hW ν
    (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg) (CorrectedWeakAnalysis.Construction.schrodingerCayleyPhase_continuous N g hg) f h
  unfold CorrectedNormalization.Construction.correctedWeakOpenCell UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian
  simp_rw [weylMatrixCoefficient_add_right hk ψ hc hu, mul_add]
  rw [integral_add (hI h₁) (hI h₂), mul_add]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeakLinearity.Construction
