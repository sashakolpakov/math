import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylResolutionOperator
import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierPairing

/-! # Ultra Weyl Energy -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.UltraWeylEnergy.Construction

noncomputable section

/-! Orthogonality of nonarchimedean Weyl coefficients, with a positive
constant independent of the varying test vector. This permits the exact
unitary radius of a Cayley operator to be read from Fourier Plancherel. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
variable (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
variable (hc : Continuous (fun t : k => ψ t)) (hu : ∀ t : k, ‖ψ t‖ = 1)

include hk hc hu in
theorem weylMatrixCoefficient_norm_swap_neg (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val u.val v‖ =
      ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val (-v)‖ := by
  rw [UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hk ψ hc hu, UnitarySplitting.Weyl.Construction.heisenbergOperator_adjoint,
    UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hk ψ hc hu]
  exact norm_inner_symm _ _

variable [IsUltrametricDist k]
variable (hn : ∃ t : k, ψ t ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure]

theorem ultraResolution_pairing_self (u f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ⟪UnitarySplitting.Weak.Construction.testToL2 k N f, UnitarySplitting.Weak.Construction.testToL2 k N (UnitarySplitting.WeylResolutionOperator.Construction.ultraResolutionLinearMap hk ψ hc hu hn ν u f)⟫_ℂ =
      ((∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val v‖ ^ 2 ∂ν : ℝ) : ℂ) := by
  rw [UnitarySplitting.Weak.Construction.testToL2_inner]
  change (∫ x, UnitarySplitting.WeylSynthesisAdd.Construction.weylSynthesis ψ ν (UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val)
    u.val x * conj (f.val x) ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure k N) = _
  rw [UnitarySplitting.WeylSynthesis.Construction.weylSynthesis_pairing ψ hc hu (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) ν _
    (UnitarySplitting.WeylResolutionOperator.Construction.weylAnalysis_locallyConstant hk ψ hc u f).continuous
    ((UnitarySplitting.WeylResolutionOperator.Construction.weylAnalysis_locallyConstant hk ψ hc u f).continuous.integrable_of_hasCompactSupport
      (UnitarySplitting.WeylResolutionOperator.Construction.weylAnalysis_compactSupport hk ψ hn u f))]
  have he (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
      UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val v *
        UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val v =
      ((‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val v‖ ^ 2 : ℝ) : ℂ) := by
    rw [UnitarySplitting.WeylAnalysis.Construction.weylAnalysis, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [he]
  exact integral_complex_ofReal

include hk hc hu hn in
theorem ultraWeylCoefficient_positive_energy (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (hu0 : u ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
      (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val u.val v‖ ^ 2 ∂ν) =
        r * Local.FunctionsMetaplectic.Construction.l2Energy k N f := by
  obtain ⟨r, hr, hres⟩ := UnitarySplitting.WeylResolutionOperator.Construction.ultraResolution_positive_scalar hk ψ hc hu hn ν u hu0
  refine ⟨r, hr, fun f => ?_⟩
  have hp := ultraResolution_pairing_self hk ψ hc hu hn ν u f
  rw [hres, map_smul, inner_smul_right, inner_self_eq_norm_sq_to_K] at hp
  have he : (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val v‖ ^ 2 ∂ν) =
      r * Local.FunctionsMetaplectic.Construction.l2Energy k N f := by
    rw [← UnitarySplitting.FourierPairing.Construction.testToL2_norm_sq]
    apply Complex.ofReal_injective
    push_cast
    exact hp.symm
  simp_rw [weylMatrixCoefficient_norm_swap_neg hk ψ hc hu f u]
  exact (integral_neg_eq_self (fun v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N =>
    ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val v‖ ^ 2) ν).trans he

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.UltraWeylEnergy.Construction
