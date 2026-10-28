import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ProjectiveTorusData

/-! # Period Duality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.PeriodDuality.CM.Abelian

noncomputable section

/-! Rational lattice characters and the covectors induced by the polarization. -/

open scoped TensorProduct

variable {U ι : Type} [AddCommGroup U] [Module ℚ U]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ U)
  (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)

def genericLatticeBasis : Module.Basis ι ℤ (ProjectiveTorusData.CM.Abelian.genericPeriodLattice b H) :=
  (ProjectiveTorusData.CM.Abelian.genericPeriodBasis b H).restrictScalars ℤ

/-- The rational dual is identified with rational-valued characters on the actual lattice. -/
def genericLatticeDualEquiv : Module.Dual ℚ U ≃ₗ[ℚ]
    (ProjectiveTorusData.CM.Abelian.genericPeriodLattice b H →ₗ[ℤ] ℚ) where
  toFun f := (genericLatticeBasis b H).constr ℤ (fun i => f (b i))
  invFun χ := b.constr ℚ (fun i => χ (genericLatticeBasis b H i))
  left_inv f := by
    apply b.ext
    intro i
    simp
  right_inv χ := by
    apply (genericLatticeBasis b H).ext
    intro i
    simp
  map_add' f g := by
    apply (genericLatticeBasis b H).ext
    intro i
    simp only [Module.Basis.constr_basis, LinearMap.add_apply]
  map_smul' q f := by
    apply (genericLatticeBasis b H).ext
    intro i
    simp

theorem genericLatticeDualEquiv_basis (f : Module.Dual ℚ U) (i : ι) :
    genericLatticeDualEquiv b H f (genericLatticeBasis b H i) = f (b i) :=
  (genericLatticeBasis b H).constr_basis ℤ _ i

def polarizationDualEquiv (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization H) : U ≃ₗ[ℚ] Module.Dual ℚ U := by
  let : Module.Finite ℚ U := H.finiteDimensional
  exact P.form.toDual P.nondegenerate

def genericPeriodRealVector : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H →ₗ[ℝ] ComplexMultiplication.WeightOne.CM.Complexification U :=
  (PeriodSpace.CM.Abelian.realPeriodSpace U).subtype.comp
    ((PeriodSpace.CM.Abelian.periodRealEquiv H).symm.toLinearMap.comp
      ((ProjectiveTorusData.CM.Abelian.periodComplexEquiv H).symm.restrictScalars ℝ).toLinearMap)

theorem genericPeriodRealVector_apply (v : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H) :
    genericPeriodRealVector H v =
      ((ProjectiveTorusData.CM.Abelian.periodComplexEquiv H).symm v : ComplexMultiplication.WeightOne.CM.Complexification U) +
        ComplexMultiplication.WeightOne.CM.coefficientConjugation U ((ProjectiveTorusData.CM.Abelian.periodComplexEquiv H).symm v) :=
  PeriodSpace.CM.Abelian.periodRealEquiv_symm_coe H _

theorem genericPeriodRealVector_basis (i : ι) :
    genericPeriodRealVector H (ProjectiveTorusData.CM.Abelian.genericPeriodBasis b H i) = (1 : ℂ) ⊗ₜ[ℚ] b i :=
  ProjectiveTorusData.CM.Abelian.genericPeriodBasis_realVector b i

variable {H} (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization H)

/-- Pairing with real period vectors gives the actual invariant covector. -/
def polarizedPeriodCovector (x : ComplexMultiplication.WeightOne.CM.Complexification U) : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H →L[ℝ] ℂ :=
  (((P.form.baseChange ℂ x).restrictScalars ℝ).comp
    (genericPeriodRealVector H)).toContinuousLinearMap

theorem polarizedPeriodCovector_apply (x : ComplexMultiplication.WeightOne.CM.Complexification U) (v : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H) :
    polarizedPeriodCovector P x v = P.form.baseChange ℂ x (genericPeriodRealVector H v) := rfl

theorem polarizedPeriodCovector_basis (x : ComplexMultiplication.WeightOne.CM.Complexification U) (i : ι) :
    polarizedPeriodCovector P x (ProjectiveTorusData.CM.Abelian.genericPeriodBasis b H i) =
      P.form.baseChange ℂ x ((1 : ℂ) ⊗ₜ[ℚ] b i) := by
  rw [polarizedPeriodCovector_apply, genericPeriodRealVector_basis]

theorem polarizedPeriodCovector_holomorphic (x : ComplexMultiplication.WeightOne.CM.Complexification U)
    (hx : x ∈ H.holomorphic) :
    ∃ L : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H →L[ℂ] ℂ, polarizedPeriodCovector P x = L.restrictScalars ℝ := by
  let L : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H →ₗ[ℂ] ℂ :=
    (P.form.baseChange ℂ x).comp
      (H.antiholomorphic.subtype.comp (ProjectiveTorusData.CM.Abelian.periodComplexEquiv H).symm.toLinearMap)
  refine ⟨L.toContinuousLinearMap, ?_⟩
  ext v
  rw [polarizedPeriodCovector_apply, genericPeriodRealVector_apply, map_add,
    P.holomorphic_isotropic x hx _ (PeriodSpace.CM.Abelian.conjugate_antiholomorphic_mem H _), add_zero]
  rfl

/-- Complex linearity detects the original holomorphic summand. -/
theorem polarizedPeriodCovector_complexLinear_iff (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    (∃ L : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H →L[ℂ] ℂ,
      polarizedPeriodCovector P x = L.restrictScalars ℝ) ↔ x ∈ H.holomorphic := by
  constructor
  · rintro ⟨L, hL⟩
    obtain ⟨a, u, rfl, _⟩ :=
      H.holomorphic.existsUnique_add_of_isCompl H.complementary x
    have hsm := L.map_smul Complex.I (ProjectiveTorusData.CM.Abelian.periodComplexEquiv H u)
    have hvalue (v : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H) :
        L v = P.form.baseChange ℂ ((a : ComplexMultiplication.WeightOne.CM.Complexification U) + u)
          (genericPeriodRealVector H v) :=
      (congrArg (fun f : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H →L[ℝ] ℂ => f v) hL).symm
    simp only [hvalue, genericPeriodRealVector_apply, map_smul,
      LinearEquiv.symm_apply_apply, PeriodSpace.CM.Abelian.coefficientConjugation_complex_smul,
      Submodule.coe_smul, smul_eq_mul, map_add] at hsm
    have hz : P.form.baseChange ℂ ((a : ComplexMultiplication.WeightOne.CM.Complexification U) + u)
        (ComplexMultiplication.WeightOne.CM.coefficientConjugation U u) = 0 := by
      have he : (2 * Complex.I) * P.form.baseChange ℂ ((a : ComplexMultiplication.WeightOne.CM.Complexification U) + u)
          (ComplexMultiplication.WeightOne.CM.coefficientConjugation U u) = 0 := by
        simp only [map_add, LinearMap.add_apply,
          Complex.star_def, Complex.conj_I] at hsm ⊢
        linear_combination -hsm
      exact (mul_eq_zero.mp he).resolve_left (by norm_num)
    rw [map_add, LinearMap.add_apply,
      P.holomorphic_isotropic _ a.property _ (PeriodSpace.CM.Abelian.conjugate_antiholomorphic_mem H u), zero_add] at hz
    have hu : u = 0 := by
      by_contra hne
      have hc : ComplexMultiplication.WeightOne.CM.coefficientConjugation U (u : ComplexMultiplication.WeightOne.CM.Complexification U) ≠ 0 := by
        intro h
        apply hne
        apply Subtype.ext
        change (u : ComplexMultiplication.WeightOne.CM.Complexification U) = 0
        have hh := congrArg (ComplexMultiplication.WeightOne.CM.coefficientConjugation U) h
        simpa only [ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive, map_zero] using hh
      have hp := P.hodge_positive _ (PeriodSpace.CM.Abelian.conjugate_antiholomorphic_mem H u) hc
      rw [ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive,
        RiemannForm.CM.Abelian.rationalAlternating_complex_skew P.form P.alternating, hz] at hp
      norm_num at hp
    simpa only [hu, Submodule.coe_zero, add_zero] using a.property
  · exact polarizedPeriodCovector_holomorphic P x

theorem genericPeriodRealVector_fixed (v : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H) :
    ComplexMultiplication.WeightOne.CM.coefficientConjugation U (genericPeriodRealVector H v) =
      genericPeriodRealVector H v :=
  ((PeriodSpace.CM.Abelian.periodRealEquiv H).symm ((ProjectiveTorusData.CM.Abelian.periodComplexEquiv H).symm v)).property

theorem polarizedPeriodCovector_conjugation (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    polarizedPeriodCovector P (ComplexMultiplication.WeightOne.CM.coefficientConjugation U x) =
      Complex.conjCLE.toContinuousLinearMap.comp (polarizedPeriodCovector P x) := by
  ext v
  change P.form.baseChange ℂ (ComplexMultiplication.WeightOne.CM.coefficientConjugation U x) (genericPeriodRealVector H v) =
    star (P.form.baseChange ℂ x (genericPeriodRealVector H v))
  rw [← RiemannForm.CM.Abelian.rationalBilin_conjugation, genericPeriodRealVector_fixed]

theorem polarizedPeriodCovector_antilinear_iff (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    (∃ L : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H →L[ℂ] ℂ,
      polarizedPeriodCovector P x =
        Complex.conjCLE.toContinuousLinearMap.comp (L.restrictScalars ℝ)) ↔
      x ∈ H.antiholomorphic := by
  have hc : ComplexMultiplication.WeightOne.CM.coefficientConjugation U x ∈ H.holomorphic ↔ x ∈ H.antiholomorphic := by
    simpa only [ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive] using
      (H.conjugate_mem (ComplexMultiplication.WeightOne.CM.coefficientConjugation U x)).symm
  rw [← hc, ← polarizedPeriodCovector_complexLinear_iff P,
    polarizedPeriodCovector_conjugation]
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L, ?_⟩
    rw [hL]
    ext v
    exact star_star _
  · rintro ⟨L, hL⟩
    refine ⟨L, ?_⟩
    ext v
    have h := congrArg (fun f : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H →L[ℝ] ℂ => star (f v)) hL
    exact (star_star _).symm.trans h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.PeriodDuality.CM.Abelian
