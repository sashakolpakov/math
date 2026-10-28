import OAI.RepresentationTheory.Weil.UnitarySplitting.Weyl
import OAI.RepresentationTheory.Weil.UnitarySplitting.TestSpaceAnalysis

/-! # Weyl Matrix Coefficients -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeylMatrixCoefficients.Construction

noncomputable section

/-! Matrix coefficients of the actual Schrödinger Weyl operators. -/

open _root_.MeasureTheory _root_.Topology Filter
open scoped InnerProductSpace ComplexConjugate

def weylMatrixCoefficient
    {F : Type} [NormedField F] [MeasurableSpace F] {d : ℕ}
    (ψ : AddChar F ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d))
    (f h : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : ℂ :=
  ∫ x, Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f x * conj (h x) ∂μ

theorem weylMatrixCoefficient_continuous
    {F : Type} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] {d : ℕ}
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [μ.IsAddHaarMeasure]
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : Continuous (weylMatrixCoefficient ψ μ f.val h.val) := by
  obtain ⟨C, -, hC⟩ := TestSpaceAnalysis.Construction.schwartzBruhat_norm_bound f.property
  have hfc := TestSpaceAnalysis.Construction.schwartzBruhat_continuous f.property
  have hhc := TestSpaceAnalysis.Construction.schwartzBruhat_continuous h.property
  have hcont : Continuous (fun p : Local.FunctionsMetaplectic.Construction.PhaseSpace F d × Local.FunctionsMetaplectic.Construction.Position F d =>
      Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ p.1 f.val p.2 * conj (h.val p.2)) := by
    unfold Local.FunctionsMetaplectic.Construction.heisenbergFunction
    fun_prop
  have hbound (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (x : Local.FunctionsMetaplectic.Construction.Position F d) :
      ‖Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val x * conj (h.val x)‖ ≤ C * ‖h.val x‖ := by
    unfold Local.FunctionsMetaplectic.Construction.heisenbergFunction
    simp only [norm_mul, hu, one_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  rw [continuous_iff_continuousAt]
  intro v
  apply tendsto_integral_filter_of_dominated_convergence (fun x => C * ‖h.val x‖)
  · exact Filter.Eventually.of_forall fun w =>
      (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun w => Filter.Eventually.of_forall (hbound w)
  · exact (TestSpaceAnalysis.Construction.schwartzBruhat_integrable μ h).norm.const_mul C
  · exact Filter.Eventually.of_forall fun x =>
      (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto

theorem weylMatrixCoefficient_eq_inner
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val h.val v =
      ⟪Weak.Construction.testToL2 F d h, Weak.Construction.testToL2 F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f)⟫_ℂ := by
  rw [Weak.Construction.testToL2_inner]
  rfl

theorem weylMatrixCoefficient_covariance
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (U : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hU : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (U f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (g : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    (hcov : ∀ v f, U (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
      HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (g v) (U f))
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) (U f).val (U h).val (g v) =
      weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val h.val v := by
  rw [weylMatrixCoefficient_eq_inner hF ψ hc hu, ← hcov]
  exact (Weak.Construction.energy_preserving_inner F d U.toLinearMap hU h (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f)).trans
    (weylMatrixCoefficient_eq_inner hF ψ hc hu f h v).symm

theorem weylMatrixCoefficient_input_shift
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (v w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
        (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f).val h.val v =
      ψ (Oscillator.Construction.standardSymplecticPairing d v w / 2) *
        weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val h.val (v + w) := by
  rw [weylMatrixCoefficient_eq_inner hF ψ hc hu, Weyl.Construction.heisenbergOperator_composition,
    map_smul, inner_smul_right, ← weylMatrixCoefficient_eq_inner hF ψ hc hu]

theorem weylMatrixCoefficient_output_shift
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (v w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val
        (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w h).val v =
      ψ (Oscillator.Construction.standardSymplecticPairing d (-w) v / 2) *
        weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val h.val (-w + v) := by
  rw [weylMatrixCoefficient_eq_inner hF ψ hc hu]
  have hh := Weyl.Construction.heisenbergOperator_inner hF ψ hc hu (-w)
    (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w h) (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f)
  rw [Weyl.Construction.heisenbergOperator_neg_cancel, Weyl.Construction.heisenbergOperator_composition, map_smul, inner_smul_right] at hh
  exact hh.symm.trans (congrArg (fun z => ψ (Oscillator.Construction.standardSymplecticPairing d (-w) v / 2) * z)
    (weylMatrixCoefficient_eq_inner hF ψ hc hu f h (-w + v)).symm)

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeylMatrixCoefficients.Construction
