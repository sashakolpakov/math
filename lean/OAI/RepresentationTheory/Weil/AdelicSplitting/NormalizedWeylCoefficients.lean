import OAI.RepresentationTheory.Weil.AdelicSplitting.WeakCayleyCoefficients
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCompositionPhase
import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylCoefficientTransport

/-! # Normalized Weyl Coefficients -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizedWeylCoefficients.Construction

noncomputable section

/-! The prescribed weak normalization determines every output Weyl
coefficient, for any Haar position measure. -/

open _root_.MeasureTheory
open scoped ComplexConjugate InnerProductSpace NNReal

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
variable (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure]
variable (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
variable (U : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N → Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (c : ℂ)
variable (hU : ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
  (∫ x, (U f).val x * conj (h.val x) ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure k N) =
    c * CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val h.val)

include hk hc hu hU in
theorem normalized_weyl_coefficient_reference (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) (U f).val h.val v =
      c * (Normalization.Construction.openCellScale k N g : ℂ)⁻¹ * (ψ (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg v) *
        ∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing k N (-((SchrodingerPairing.Construction.openCellDifference k N g hg).symm v)) w) *
          (ψ (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg w) *
            UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val w) ∂ν) := by
  rw [UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hk ψ hc hu, UnitarySplitting.Weyl.Construction.heisenbergOperator_adjoint,
    UnitarySplitting.Weak.Construction.testToL2_inner, hU, WeakCayleyCoefficients.Construction.correctedWeakOpenCell_coefficient_formula hk ψ hc hu]
  have hq : SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg (-v) = SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg v :=
    UnitarySplitting.CayleyCompositionPhase.Construction.cayleyWeylPhase_neg _ _ v
  rw [hq, map_neg, mul_assoc]

omit [CompleteSpace k] [LocallyCompactSpace k] [CharZero k] [BorelSpace k]
  [SecondCountableTopology k] in
theorem weylMatrixCoefficient_smul_measure (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k N)) (r : ℝ≥0)
    (f h : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (r • μ) f h v = (r : ℂ) * UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f h v := by
  unfold UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient
  rw [integral_smul_nnreal_measure]
  rfl

include hk hc hu hU in
theorem normalized_weyl_coefficient_haar (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure]
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ (U f).val h.val v =
      c * (Normalization.Construction.openCellScale k N g : ℂ)⁻¹ * (ψ (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg v) *
        ∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing k N (-((SchrodingerPairing.Construction.openCellDifference k N g hg).symm v)) w) *
          (ψ (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg w) * UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val w) ∂ν) := by
  let r := Measure.addHaarScalarFactor μ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
  have hm : μ = r • UnitarySplitting.Weak.Construction.referencePositionMeasure k N :=
    Measure.isAddLeftInvariant_eq_smul_of_regular μ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
  rw [hm, weylMatrixCoefficient_smul_measure,
    normalized_weyl_coefficient_reference hk ψ hc hu ν g hg U c hU]
  simp only [weylMatrixCoefficient_smul_measure]
  have hi : (∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing k N (-((SchrodingerPairing.Construction.openCellDifference k N g hg).symm v)) w) *
      (ψ (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg w) *
        ((r : ℂ) * UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val w)) ∂ν) =
      (r : ℂ) * ∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing k N (-((SchrodingerPairing.Construction.openCellDifference k N g hg).symm v)) w) *
        (ψ (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg w) *
          UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val w) ∂ν := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => by ring
  rw [hi]
  ring

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizedWeylCoefficients.Construction
