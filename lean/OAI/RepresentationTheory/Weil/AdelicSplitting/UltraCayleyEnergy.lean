import OAI.RepresentationTheory.Weil.AdelicSplitting.PhaseFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.UltraWeylEnergy
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyMatrixCoefficient

/-! # Ultra Cayley Energy -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.UltraCayleyEnergy.Construction

noncomputable section

/-! Exact energy scaling of the nonarchimedean Cayley operator. The
determinant is derived from Fourier Plancherel and Weyl orthogonality. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyMatrixCoefficient.Construction _root_.MeasureTheory
open scoped _root_.Matrix

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] [IsUltrametricDist k] {N : ℕ}
variable (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
variable (hc : Continuous (fun t : k => ψ t)) (hu : ∀ t : k, ‖ψ t‖ = 1) (hn : ∃ t : k, ψ t ≠ 1)
variable (μ : Measure k) [μ.IsAddHaarMeasure]
variable (hStable : ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k (N + N),
  Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin (N + N) => μ)) f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k (N + N))
variable (hInv : ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k (N + N)) x,
  Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin (N + N) => μ))
    (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin (N + N) => μ)) f.val) x = f.val (-x))
variable (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)

def matrixUltraCayleyOperator : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat k N :=
  UnitarySplitting.UltraCayleyOperator.Construction.ultraCayleyOperator hk ψ hc hu hn (Measure.pi (fun _ : Fin N ⊕ Fin N => μ))
    (CorrectedNormalization.Construction.standardSymplecticOfMatrix k N g) (SchrodingerPairing.Construction.openCellDifference k N g hg)
    (SchrodingerPairing.Construction.openCellDifference_apply k N g hg)

include hStable hInv in
theorem matrixUltraCayley_coefficient_energy (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
      (matrixUltraCayleyOperator hk ψ hc hu hn μ g hg f).val u.val v‖ ^ 2
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) =
    (DeterminantMeasure.LocalAnalysis.haarModulus k (g.val - 1).det : ℝ) *
      ∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val u.val v‖ ^ 2
        ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ) := by
  let ν := Measure.pi (fun _ : Fin N ⊕ Fin N => μ)
  let : ν.IsAddHaarMeasure := by dsimp [ν]; infer_instance
  let D := SchrodingerPairing.Construction.openCellDifference k N g hg
  let q := UnitarySplitting.CayleyCompositionPhase.Construction.cayleyWeylPhase (UnitarySplitting.StandardTransvections.Construction.standardSymplecticBilinear k N) D
  let φ : Local.FunctionsMetaplectic.Construction.PhaseSpace k N → ℂ := fun v => ψ (q v) *
    UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val u.val v
  let T : Local.FunctionsMetaplectic.Construction.PhaseSpace k N → ℂ := fun v => ∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing k N v w) * φ w ∂ν
  have hq : Continuous q := UnitarySplitting.CayleySynthesisPairing.Construction.standardCayleyWeylPhase_continuous hk D
  have hφl : IsLocallyConstant φ :=
    ((UnitarySplitting.LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hc).comp_continuous hq).mul
      (UnitarySplitting.UltraWeylCoefficients.Construction.weylMatrixCoefficient_locallyConstant_ultra hk ψ hc (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f u)
  have hφs : HasCompactSupport φ :=
    (UnitarySplitting.WeylSynthesisAdd.Construction.weylMatrixCoefficient_compactSupport_ultra hk ψ hn (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f u).mul_left
  have hφ : (fun x => φ ((PhaseMeasure.Construction.phaseCoordinates k N).symm x)) ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k (N + N) :=
    Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem (hφl.comp_continuous (PhaseMeasure.Construction.phaseCoordinates k N).symm.continuous)
      (hφs.comp_homeomorph (PhaseMeasure.Construction.phaseCoordinates k N).symm.toHomeomorph)
  have hT : (∫ v, ‖T v‖ ^ 2 ∂ν) = ∫ v, ‖φ v‖ ^ 2 ∂ν :=
    PhaseFourier.Construction.phaseFourier_norm_sq k N ψ hu hc μ hStable hInv φ hφ
  have hcoeff (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
      ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
        (matrixUltraCayleyOperator hk ψ hc hu hn μ g hg f).val u.val v‖ = ‖T (-D.symm v)‖ := by
    rw [matrixUltraCayleyOperator, UnitarySplitting.UltraCayleyMatrixCoefficient.Construction.ultraCayleyOperator_matrixCoefficient hk ψ hc hu hn ν
      (CorrectedNormalization.Construction.standardSymplecticOfMatrix k N g) D (SchrodingerPairing.Construction.openCellDifference_apply k N g hg), norm_mul, hu, one_mul]
    unfold T φ
    rw [CorrectedNormalization.Construction.schrodingerPairing_eq_standardBilinear]
  have hD (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) : D.symm v = (g.val - 1)⁻¹ *ᵥ v := by
    change (Matrix.toLin (Pi.basisFun k (Fin N ⊕ Fin N))
      (Pi.basisFun k (Fin N ⊕ Fin N)) (g.val - 1)⁻¹) v = _
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  simp_rw [hcoeff, hD]
  rw [PhaseMeasure.Construction.phaseMatrix_inverse_integral k μ (g.val - 1) hg (fun v => ‖T (-v)‖ ^ 2),
    integral_neg_eq_self (fun v => ‖T v‖ ^ 2) ν, hT]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    simp only [φ, norm_mul, hu, one_mul]

include hStable hInv in
theorem matrixUltraCayley_energy (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    Local.FunctionsMetaplectic.Construction.l2Energy k N (matrixUltraCayleyOperator hk ψ hc hu hn μ g hg f) =
      (DeterminantMeasure.LocalAnalysis.haarModulus k (g.val - 1).det : ℝ) * Local.FunctionsMetaplectic.Construction.l2Energy k N f := by
  obtain ⟨u, hu0⟩ := UnitarySplitting.LocalTest.Construction.exists_test_nonzero k hk N
  obtain ⟨r, hr, henergy⟩ := UltraWeylEnergy.Construction.ultraWeylCoefficient_positive_energy hk ψ hc hu hn
    (Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) u hu0
  have he := matrixUltraCayley_coefficient_energy hk ψ hc hu hn μ hStable hInv g hg f u
  rw [henergy, henergy, ← mul_assoc, mul_comm (DeterminantMeasure.LocalAnalysis.haarModulus k (g.val - 1).det : ℝ) r,
    mul_assoc] at he
  exact mul_left_cancel₀ hr.ne' he

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.UltraCayleyEnergy.Construction
