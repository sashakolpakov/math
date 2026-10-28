import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesisAdd

/-! # Weyl Synthesis -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesis.Construction

noncomputable section

section

/-! Pairing a Weyl superposition with a test vector is the integral of
the corresponding Weyl matrix coefficient. -/

open _root_.MeasureTheory _root_.Topology Filter
open scoped ComplexConjugate

theorem weylSynthesis_pairing
    {F : Type} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] {d : ℕ}
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [μ.IsAddHaarMeasure] [SigmaFinite μ]
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [SigmaFinite ν]
    (a : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ) (ha : Continuous a) (hai : Integrable a ν)
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    (∫ x, WeylSynthesisAdd.Construction.weylSynthesis ψ ν a f.val x * conj (h.val x) ∂μ) =
      ∫ v, a v * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val v ∂ν := by
  obtain ⟨C, hCpos, hC⟩ := TestSpaceAnalysis.Construction.schwartzBruhat_norm_bound f.property
  have hfc := TestSpaceAnalysis.Construction.schwartzBruhat_continuous f.property
  have hhc := TestSpaceAnalysis.Construction.schwartzBruhat_continuous h.property
  let k : Local.FunctionsMetaplectic.Construction.PhaseSpace F d × Local.FunctionsMetaplectic.Construction.Position F d → ℂ :=
    fun p => a p.1 * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ p.1 f.val p.2 * conj (h.val p.2)
  have hkc : Continuous k := by unfold k Local.FunctionsMetaplectic.Construction.heisenbergFunction; fun_prop
  have hki : Integrable k (ν.prod μ) := by
    apply ((hai.norm.mul_const C).mul_prod (TestSpaceAnalysis.Construction.schwartzBruhat_integrable μ h).norm).mono
      hkc.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      change ‖a p.1 * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ p.1 f.val p.2 * conj (h.val p.2)‖ ≤
        ‖(‖a p.1‖ * C) * ‖h.val p.2‖‖
      unfold Local.FunctionsMetaplectic.Construction.heisenbergFunction
      simp only [norm_mul, hu, one_mul, RCLike.norm_conj, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCpos]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)) (norm_nonneg _)
  calc
    _ = ∫ x, ∫ v, a v * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val x * conj (h.val x) ∂ν ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only [WeylSynthesisAdd.Construction.weylSynthesis]
        rw [integral_mul_const]
    _ = ∫ v, ∫ x, a v * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val x * conj (h.val x) ∂μ ∂ν :=
      (integral_integral_swap hki).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        dsimp only [WeylMatrixCoefficients.Construction.weylMatrixCoefficient]
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by dsimp only; ring

end

/-! Synthesis in the conjugate-linear slot of a Weyl matrix coefficient. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

theorem weylMatrixCoefficient_synthesized_output
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [SigmaFinite ν]
    (a : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ) (ha : Continuous a) (hai : Integrable a ν)
    (f u h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (hh : h.val = WeylSynthesisAdd.Construction.weylSynthesis ψ ν a u.val)
    (w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val h.val w =
      ∫ v, conj (a v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
        f.val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v u).val w ∂ν := by
  have hp : ⟪Weak.Construction.testToL2 F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f), Weak.Construction.testToL2 F d h⟫_ℂ =
      ∫ v, a v * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
        u.val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f).val v ∂ν := by
    rw [Weak.Construction.testToL2_inner, hh]
    exact weylSynthesis_pairing ψ hc hu (Weak.Construction.referencePositionMeasure F d) ν a ha hai
      u (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f)
  calc
    _ = conj ⟪Weak.Construction.testToL2 F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f), Weak.Construction.testToL2 F d h⟫_ℂ := by
      rw [inner_conj_symm, WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu]
    _ = _ := by
      rw [hp, ← integral_conj]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        dsimp only
        rw [map_mul, WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu,
          inner_conj_symm, WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesis.Construction
