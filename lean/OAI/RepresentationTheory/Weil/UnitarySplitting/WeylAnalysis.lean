import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesis
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCompositionPhase
import OAI.RepresentationTheory.Weil.UnitarySplitting.StandardTransvections

/-! # Weyl Analysis -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeylAnalysis.Construction

noncomputable section

/-! Weyl analysis coefficients, linear in the analyzed test vector. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

def weylAnalysis
    {F : Type} [NormedField F] [MeasurableSpace F] {d : ℕ}
    (ψ : AddChar F ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d))
    (u f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : ℂ :=
  conj (WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ u f v)

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)

theorem weylAnalysis_eq_inner (u f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val f.val v =
      ⟪Weak.Construction.testToL2 F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v u), Weak.Construction.testToL2 F d f⟫_ℂ := by
  rw [weylAnalysis, WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu, inner_conj_symm]

include hF hc hu in
theorem weylAnalysis_add (u f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val (f + h).val =
      weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val f.val +
        weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val h.val := by
  funext v
  simp only [weylAnalysis_eq_inner hF ψ hc hu, map_add, inner_add_right, Pi.add_apply]

include hF hc hu in
theorem weylAnalysis_smul (u f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (z : ℂ) :
    weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val (z • f).val =
      z • weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val f.val := by
  funext v
  simp only [weylAnalysis_eq_inner hF ψ hc hu, map_smul, inner_smul_right, Pi.smul_apply, smul_eq_mul]

theorem weylAnalysis_input_shift (u f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (v w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f).val v =
      ψ (Oscillator.Construction.standardSymplecticPairing d w v / 2) *
        weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val f.val (v - w) := by
  unfold weylAnalysis
  rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_output_shift hF ψ hc hu, map_mul,
    ← Complex.inv_eq_conj (hu _), ← ψ.map_neg_eq_inv]
  have hphase : -(Oscillator.Construction.standardSymplecticPairing d (-w) v / 2) =
      Oscillator.Construction.standardSymplecticPairing d w v / 2 := by
    change -((StandardTransvections.Construction.standardSymplecticBilinear F d) (-w) v / 2) = _
    rw [map_neg, LinearMap.neg_apply, neg_div, neg_neg]
    rfl
  have hshift : -w + v = v - w := by abel
  rw [hphase, hshift]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeylAnalysis.Construction
