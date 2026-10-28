import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FourSplittings
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientPeriods

/-! # Transport New -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TransportNew.CM

noncomputable section

section

/-! Actual line periods for the two new rational lines. Their Hermitian
coefficients and imaginary trace scalar come from the original space. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open _root_.Module

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

omit [IsGalois ℚ K] in
theorem multiplicity_norm_fixed (a : Fin 2 → K)
    (ha : ∀ i, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (a i) = a i) (x : Analysis.DifferentialForms.Coordinates.LocalApproximation.W K) :
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a x x) = Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a x x := by
  change NumberField.IsCMField.complexConj K (Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a x x) = _
  have ha' : ∀ i, NumberField.IsCMField.complexConj K (a i) = a i := ha
  simp only [Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian, map_sum, map_mul, ha',
    NumberField.IsCMField.complexConj_apply_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem new_line_periods_on_original_space
    (dOld dNew : Fin 2 → Gal(K/ℚ) → Bool)
    (P : Lagrangians.CM.LagrangianPair K B places (fun i τ => dOld i (places.representative τ)))
    (hμ : ∀ i, dNew i 1 = true)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (hnd : ∀ i, Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian P.a (b i) (b i) ≠ 0)
    (hs : ∀ i τ, 0 < (ComplexMultiplication.SignSwitch.CM.signValue (dNew i (places.representative τ)) : ℝ) *
      (-(HeckeCycles.ReferenceDatum.CM.embeddings K places τ P.delta).im) *
        (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian P.a (b i) (b i))).re) :
    ∃ L : (i : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (dNew i),
      ∀ i, (L i).coordinates.a = Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian P.a (b i) (b i) ∧
        (L i).coordinates.delta = P.delta := by
  let a : Fin 2 → K := fun i => Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian P.a (b i) (b i)
  have ha : ∀ i, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (a i) = a i :=
    fun i => multiplicity_norm_fixed K P.a (fun j => (P.a_sign j).2.1) (b i)
  have hr (τ : Fin places.count) : (HeckeCycles.ReferenceDatum.CM.embeddings K places τ P.delta).re = 0 := by
    simpa only [mul_one] using Geometry.ComplexBall.PrescribedSignsB.coefficient_real_zero
      (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) P.delta 1 P.delta_imaginary (map_one _)
  have hsign (i : Fin 2) (τ : Fin places.count) :
      if τ = places.distinguished ∨ dNew i (places.representative τ) = true
        then (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (P.delta * a i)).im < 0
        else 0 < (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (P.delta * a i)).im := by
    have ht := hs i τ
    change 0 < (ComplexMultiplication.SignSwitch.CM.signValue (dNew i (places.representative τ)) : ℝ) *
      (-(HeckeCycles.ReferenceDatum.CM.embeddings K places τ P.delta).im) * (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (a i)).re at ht
    rw [map_mul, Complex.mul_im, hr, zero_mul, zero_add]
    by_cases hd : dNew i (places.representative τ) = true
    · simp only [hd, or_true, ite_true]
      simp [hd, ComplexMultiplication.SignSwitch.CM.signValue] at ht
      nlinarith
    · have hτ : τ ≠ places.distinguished := by
        intro he
        apply hd
        simpa only [he, places.identity] using hμ i
      have hd' : dNew i (places.representative τ) = false := Bool.eq_false_iff.mpr hd
      simp [hτ, hd]
      simpa [hd', ComplexMultiplication.SignSwitch.CM.signValue] using ht
  obtain ⟨Q, hδQ, haQ⟩ := CoefficientPeriods.CM.exists_lagrangian_pair_with_coefficients K B places
    (fun i τ => dNew i (places.representative τ)) P.delta a P.delta_ne_zero
    P.delta_imaginary hnd ha hsign
  choose L hL using (fun i => LinePeriods.CM.exists_line_period K dNew Q i)
  refine ⟨L, fun i => ?_⟩
  exact ⟨(hL i).1.trans (congrFun haQ i), (hL i).2.trans hδQ⟩

end

section

/-! The rational basis change is an isometry from the new diagonal
coefficients to the original Hermitian multiplicity space. -/

open scoped Classical
open _root_.Module

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]

theorem multiplicity_hermitian_symm (a : Fin 2 → K)
    (ha : ∀ i, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (a i) = a i) (x y : Analysis.DifferentialForms.Coordinates.LocalApproximation.W K) :
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a x y) = Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a y x := by
  change NumberField.IsCMField.complexConj K (Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a x y) = _
  have ha' : ∀ i, NumberField.IsCMField.complexConj K (a i) = a i := ha
  simp only [Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian, map_sum, map_mul, ha',
    NumberField.IsCMField.complexConj_apply_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem multiplicity_hermitian_add_left (a : Fin 2 → K) (x y z : Analysis.DifferentialForms.Coordinates.LocalApproximation.W K) :
    Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (x + y) z =
      Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a x z + Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a y z := by
  simp [Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian, mul_add, add_mul, Finset.sum_add_distrib]

theorem multiplicity_hermitian_smul_left (a : Fin 2 → K) (x y : Analysis.DifferentialForms.Coordinates.LocalApproximation.W K) (r : K) :
    Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (r • x) y = r * Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a x y := by
  simp only [Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem multiplicity_basis_isometry (a : Fin 2 → K)
    (ha : ∀ i, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (a i) = a i)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (horth : Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) (b 1) = 0)
    (x y : Analysis.DifferentialForms.Coordinates.LocalApproximation.W K) :
    Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b.equivFun.symm x) (b.equivFun.symm y) =
      Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian
        (fun i => Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b i) (b i)) x y := by
  have h10 : Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 1) (b 0) = 0 := by
    rw [← multiplicity_hermitian_symm K a ha, horth, map_zero]
  rw [b.equivFun_symm_apply, b.equivFun_symm_apply]
  simp only [Fin.sum_univ_two, multiplicity_hermitian_add_left,
    Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian_add_right, multiplicity_hermitian_smul_left,
    Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian_smul_right, horth, h10, mul_zero, add_zero, zero_add]
  simp only [Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian, Fin.sum_univ_two]
  ring

end

/-! The same rational Hermitian space V tensor W in the old and new
orthogonal coordinates, including its actual trace symplectic form. -/

open scoped Classical
open _root_.Module

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]

abbrev TensorPositions := Fin 3 → Analysis.DifferentialForms.Coordinates.LocalApproximation.W K

def tensorBasisChange (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) :
    TensorPositions K ≃ₗ[K] TensorPositions K :=
  LinearEquiv.piCongrRight (fun _ : Fin 3 => b.equivFun.symm)

def tensorHermitian (β : K) (a : Fin 2 → K) (x y : TensorPositions K) : K :=
  ∑ j : Fin 3, (if j = 2 then β else 1) * Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (x j) (y j)

theorem tensor_hermitian_blocks (β : K) (a : Fin 2 → K) (x y : TensorPositions K) :
    tensorHermitian K β a x y =
      ∑ i : Fin 2, a i * HeckeCycles.GeometricSource.CM.hermitian K β (fun j => x j i) (fun j => y j i) := by
  simp only [tensorHermitian, Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian, HeckeCycles.GeometricSource.CM.hermitian,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change _ * (a i * x j i * NumberField.IsCMField.complexConj K (y j i)) =
    a i * (_ * x j i * NumberField.IsCMField.complexConj K (y j i))
  ring

theorem tensor_basis_isometry (β : K) (a : Fin 2 → K)
    (ha : ∀ i, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (a i) = a i)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (horth : Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) (b 1) = 0)
    (x y : TensorPositions K) :
    tensorHermitian K β a (tensorBasisChange K b x) (tensorBasisChange K b y) =
      tensorHermitian K β (fun i => Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b i) (b i)) x y := by
  apply Finset.sum_congr rfl
  intro j _
  change _ * Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b.equivFun.symm (x j)) (b.equivFun.symm (y j)) = _
  rw [multiplicity_basis_isometry K a ha b horth]

theorem tensor_trace_basis_isometry (β δ : K) (a : Fin 2 → K)
    (ha : ∀ i, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (a i) = a i)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (horth : Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) (b 1) = 0)
    (x y : TensorPositions K) :
    Algebra.trace ℚ K (δ * tensorHermitian K β a (tensorBasisChange K b x) (tensorBasisChange K b y)) =
      Algebra.trace ℚ K (δ * tensorHermitian K β
        (fun i => Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b i) (b i)) x y) := by
  rw [tensor_basis_isometry K β a ha b horth]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TransportNew.CM
