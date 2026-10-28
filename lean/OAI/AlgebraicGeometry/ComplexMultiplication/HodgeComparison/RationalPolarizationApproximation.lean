import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BilinearRational

/-! # Rational Polarization Approximation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalPolarizationApproximation.CM.Construction

noncomputable section

/-! Rational approximation inside a finite family of rational alternating
forms preserves strict Hodge positivity and hence produces a polarization. -/

open scoped TensorProduct

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

def hodgePairFamily (B : ι → LinearMap.BilinForm ℚ U) (j : E →ₗ[ℝ] WeightOne.CM.Complexification U)
    (t : ι → ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, t i • BilinearRational.CM.Construction.rationalFormHodgeContinuousPair (B i) j

theorem hodgePairFamily_continuous (B : ι → LinearMap.BilinForm ℚ U)
    (j : E →ₗ[ℝ] WeightOne.CM.Complexification U) : Continuous (hodgePairFamily B j) := by
  let : ContinuousAdd (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : IsTopologicalAddGroup (E →L[ℝ] E →L[ℝ] ℝ)).toContinuousAdd
  unfold hodgePairFamily
  exact continuous_finsetSum (M := E →L[ℝ] E →L[ℝ] ℝ) Finset.univ
    (fun i _ => (continuous_apply i).smul continuous_const)

theorem hodgePairFamily_apply (B : ι → LinearMap.BilinForm ℚ U)
    (j : E →ₗ[ℝ] WeightOne.CM.Complexification U) (t : ι → ℝ) (u v : E) :
    hodgePairFamily B j t u v =
      (Complex.I * ∑ i, (t i : ℂ) * (B i).baseChange ℂ (j u) (WeightOne.CM.coefficientConjugation U (j v))).re := by
  simp only [hodgePairFamily, sum_apply, smul_apply, smul_eq_mul,
    BilinearRational.CM.Construction.rationalFormHodgeContinuousPair_apply, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_left_comm, Complex.re_ofReal_mul]

theorem exists_rational_polarization_combination (H : WeightOne.CM.WeightOneHodgeStructure U)
    (B : ι → LinearMap.BilinForm ℚ U)
    (hB : ∀ i, (B i).IsAlt)
    (hiso : ∀ i, ∀ u ∈ H.holomorphic, ∀ v ∈ H.holomorphic, (B i).baseChange ℂ u v = 0)
    (j : E →ₗ[ℝ] WeightOne.CM.Complexification U) (hji : Function.Injective j)
    (hjmem : ∀ v, j v ∈ H.holomorphic)
    (hjsurj : ∀ u ∈ H.holomorphic, ∃ v, j v = u)
    (t : ι → ℝ)
    (hpos : ∀ u ∈ H.holomorphic, u ≠ 0 →
      0 < (Complex.I * ∑ i, (t i : ℂ) * (B i).baseChange ℂ u (WeightOne.CM.coefficientConjugation U u)).re) :
    ∃ q : ι → ℚ, ∃ P : CM.Polarization.WeightOnePolarization H, P.form = ∑ i, q i • B i := by
  classical
  have ht : ∀ v : E, v ≠ 0 → 0 < hodgePairFamily B j t v v := by
    intro v hv
    rw [hodgePairFamily_apply]
    apply hpos _ (hjmem v)
    intro hz
    exact hv (hji (hz.trans j.map_zero.symm))
  obtain ⟨q, hq⟩ := RationalPositiveApproximation.CM.Construction.exists_rational_positive_parameters (hodgePairFamily B j)
    (hodgePairFamily_continuous B j) t ht
  have halt : (∑ i, q i • B i).IsAlt := by
    intro u
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    exact Finset.sum_eq_zero (fun i _ => by rw [hB i u, smul_zero])
  have hiso' : ∀ u ∈ H.holomorphic, ∀ v ∈ H.holomorphic,
      (∑ i, q i • B i).baseChange ℂ u v = 0 := by
    intro u hu v hv
    rw [BilinearRational.CM.Construction.rationalBilinear_combination_baseChange]
    exact Finset.sum_eq_zero (fun i _ => by rw [hiso i u hu v hv, mul_zero])
  have hpos' : ∀ u ∈ H.holomorphic, u ≠ 0 →
      0 < (Complex.I * (∑ i, q i • B i).baseChange ℂ u (WeightOne.CM.coefficientConjugation U u)).re := by
    intro u hu hne
    obtain ⟨v, rfl⟩ := hjsurj u hu
    have hv : v ≠ 0 := by intro hz; exact hne (hz ▸ j.map_zero)
    have hp := hq v hv
    rw [hodgePairFamily_apply] at hp
    rw [BilinearRational.CM.Construction.rationalBilinear_combination_baseChange]
    exact hp
  exact ⟨q, PolarizationFromPositiveForm.CM.Construction.weightOnePolarizationOfPositive H _ halt hiso' hpos', rfl⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem exists_rational_polarization_of_real_combination (H : WeightOne.CM.WeightOneHodgeStructure U)
    (B : ι → LinearMap.BilinForm ℚ U)
    (hB : ∀ i, (B i).IsAlt)
    (hiso : ∀ i, ∀ u ∈ H.holomorphic, ∀ v ∈ H.holomorphic, (B i).baseChange ℂ u v = 0)
    (t : ι → ℝ)
    (hpos : ∀ u ∈ H.holomorphic, u ≠ 0 →
      0 < (Complex.I * ∑ i, (t i : ℂ) * (B i).baseChange ℂ u (WeightOne.CM.coefficientConjugation U u)).re) :
    ∃ q : ι → ℚ, ∃ P : CM.Polarization.WeightOnePolarization H, P.form = ∑ i, q i • B i := by
  let : FiniteDimensional ℚ U := H.finiteDimensional
  let b := Module.finBasis ℂ H.holomorphic
  let j : (Fin (Module.finrank ℂ H.holomorphic) → ℂ) →ₗ[ℝ] WeightOne.CM.Complexification U :=
    (H.holomorphic.subtype.comp b.equivFun.symm.toLinearMap).restrictScalars ℝ
  apply exists_rational_polarization_combination H B hB hiso j
    (H.holomorphic.subtype_injective.comp b.equivFun.symm.injective)
    (fun v => (b.equivFun.symm v).property) ?_ t hpos
  intro u hu
  refine ⟨b.equivFun ⟨u, hu⟩, ?_⟩
  change (b.equivFun.symm (b.equivFun ⟨u, hu⟩) : WeightOne.CM.Complexification U) = u
  rw [LinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalPolarizationApproximation.CM.Construction
