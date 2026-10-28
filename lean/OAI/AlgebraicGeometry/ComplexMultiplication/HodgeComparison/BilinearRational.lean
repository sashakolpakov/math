import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizationFromPositiveForm
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalPositiveApproximation
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-! # Bilinear Rational -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BilinearRational.CM.Construction

noncomputable section

section

/-! Real continuous Hodge pairings and scalar extension of finite
rational combinations of bilinear forms. -/

open scoped TensorProduct

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

theorem coefficientConjugation_complex_smul (z : ℂ) (u : WeightOne.CM.Complexification U) :
    WeightOne.CM.coefficientConjugation U (z • u) = star z • WeightOne.CM.coefficientConjugation U u := by
  induction u using TensorProduct.inductionOn with
  | tmul w x =>
      simp only [TensorProduct.smul_tmul', smul_eq_mul, WeightOne.CM.coefficientConjugation_tmul, star_mul]
      rw [mul_comm]
  | add u v hu hv => simp [smul_add, hu, hv]

theorem coefficientConjugation_real_smul (r : ℝ) (u : WeightOne.CM.Complexification U) :
    WeightOne.CM.coefficientConjugation U (r • u) = r • WeightOne.CM.coefficientConjugation U u := by
  have h := coefficientConjugation_complex_smul (r : ℂ) u
  rw [Complex.star_def, Complex.conj_ofReal] at h
  have hs (v : WeightOne.CM.Complexification U) : (r : ℂ) • v = r • v :=
    IsScalarTower.algebraMap_smul ℂ r v
  rw [hs, hs] at h
  exact h

theorem rationalBilinear_combination_baseChange {ι : Type*} [Fintype ι]
    (B : ι → LinearMap.BilinForm ℚ U) (q : ι → ℚ) (u v : WeightOne.CM.Complexification U) :
    (∑ i, q i • B i).baseChange ℂ u v = ∑ i, (q i : ℂ) * (B i).baseChange ℂ u v := by
  classical
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
      induction v using TensorProduct.inductionOn with
      | tmul w y =>
          simp only [LinearMap.BilinForm.baseChange_tmul, LinearMap.sum_apply,
            LinearMap.smul_apply, smul_eq_mul]
          rw [Finset.sum_smul]
          apply Finset.sum_congr rfl
          intro i _
          simp only [Rat.smul_def, Rat.cast_mul, mul_assoc]
      | add v w hv hw => simp [hv, hw, mul_add, Finset.sum_add_distrib]
  | add u v hu hv => simp [hu, hv, mul_add, Finset.sum_add_distrib]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def rationalFormHodgePair (B : LinearMap.BilinForm ℚ U) (j : E →ₗ[ℝ] WeightOne.CM.Complexification U) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => (Complex.I * B.baseChange ℂ (j u)
    (WeightOne.CM.coefficientConjugation U (j v))).re)
    (by intro u v w; simp [mul_add])
    (by
      intro r u v
      rw [map_smul, LinearMap.map_smul_of_tower, LinearMap.smul_apply, Complex.real_smul, mul_left_comm,
        Complex.re_ofReal_mul]
      rfl)
    (by intro u v w; simp [mul_add])
    (by
      intro r u v
      rw [map_smul, coefficientConjugation_real_smul, LinearMap.map_smul_of_tower, Complex.real_smul,
        mul_left_comm, Complex.re_ofReal_mul]
      rfl)

def rationalFormHodgeContinuousPair (B : LinearMap.BilinForm ℚ U)
    (j : E →ₗ[ℝ] WeightOne.CM.Complexification U) : E →L[ℝ] E →L[ℝ] ℝ :=
  (rationalFormHodgePair B j).toContinuousBilinearMap

theorem rationalFormHodgeContinuousPair_apply (B : LinearMap.BilinForm ℚ U)
    (j : E →ₗ[ℝ] WeightOne.CM.Complexification U) (u v : E) :
    rationalFormHodgeContinuousPair B j u v =
      (Complex.I * B.baseChange ℂ (j u) (WeightOne.CM.coefficientConjugation U (j v))).re := rfl

end

section

/-! Coordinates of a rational vector-valued bilinear pairing and
reconstruction of a complex functional from its rational-basis values. -/

open scoped TensorProduct

variable {U W : Type*} [AddCommGroup U] [Module ℚ U]
  [AddCommGroup W] [Module ℚ W] {ι : Type*} [Fintype ι]

def rationalBilinearCoordinate (F : U →ₗ[ℚ] U →ₗ[ℚ] W) (b : Module.Basis ι ℚ W)
    (i : ι) : LinearMap.BilinForm ℚ U := F.compr₂ (b.coord i)

omit [Fintype ι] in
theorem rationalBilinearCoordinate_baseChange (F : U →ₗ[ℚ] U →ₗ[ℚ] W)
    (b : Module.Basis ι ℚ W) (i : ι) (u v : WeightOne.CM.Complexification U) :
    (rationalBilinearCoordinate F b i).baseChange ℂ u v =
      (b.baseChange ℂ).repr (LinearMap.BilinMap.baseChange ℂ F u v) i := by
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
      induction v using TensorProduct.inductionOn with
      | tmul w y =>
          rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinMap.baseChange_tmul,
            Module.Basis.baseChange_repr_tmul]
          rfl
      | add v w hv hw => simp [hv, hw]
  | add u v hu hv => simp [hu, hv]

theorem rationalBilinear_functional_expansion (F : U →ₗ[ℚ] U →ₗ[ℚ] W)
    (b : Module.Basis ι ℚ W) (T : WeightOne.CM.Complexification W →ₗ[ℂ] ℂ)
    (u v : WeightOne.CM.Complexification U) :
    T (LinearMap.BilinMap.baseChange ℂ F u v) =
      ∑ i, T ((1 : ℂ) ⊗ₜ[ℚ] b i) * (rationalBilinearCoordinate F b i).baseChange ℂ u v := by
  classical
  let z := LinearMap.BilinMap.baseChange ℂ F u v
  have h := congrArg T ((b.baseChange ℂ).sum_repr z)
  rw [map_sum] at h
  simp only [map_smul, smul_eq_mul, Module.Basis.baseChange_apply] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [rationalBilinearCoordinate_baseChange, mul_comm]

theorem rationalBilinear_real_functional_expansion (F : U →ₗ[ℚ] U →ₗ[ℚ] W)
    (b : Module.Basis ι ℚ W) (T : WeightOne.CM.Complexification W →ₗ[ℂ] ℂ)
    (hT : ∀ w : W, (T ((1 : ℂ) ⊗ₜ[ℚ] w)).im = 0)
    (u v : WeightOne.CM.Complexification U) :
    T (LinearMap.BilinMap.baseChange ℂ F u v) =
      ∑ i, ((T ((1 : ℂ) ⊗ₜ[ℚ] b i)).re : ℂ) *
        (rationalBilinearCoordinate F b i).baseChange ℂ u v := by
  rw [rationalBilinear_functional_expansion F b T u v]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Complex.ext
  · rfl
  · exact hT (b i)

end

/-! Comparing a vector-valued rational bilinear map with an actual
complex bilinear map only requires comparison on rational simple tensors. -/

open scoped TensorProduct

variable {U W C D : Type*} [AddCommGroup U] [Module ℚ U]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup C] [Module ℂ C]
  [AddCommGroup D] [Module ℂ D]

theorem complexLinearMap_tmul (f : WeightOne.CM.Complexification U →ₗ[ℂ] C) (z : ℂ) (x : U) :
    f (z ⊗ₜ[ℚ] x) = z • f ((1 : ℂ) ⊗ₜ[ℚ] x) := by
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem bilinearScalarExtension_comparison (F : U →ₗ[ℚ] U →ₗ[ℚ] W)
    (G : C →ₗ[ℂ] C →ₗ[ℂ] D)
    (eU : WeightOne.CM.Complexification U →ₗ[ℂ] C) (eW : WeightOne.CM.Complexification W →ₗ[ℂ] D)
    (h : ∀ x y, G (eU ((1 : ℂ) ⊗ₜ[ℚ] x)) (eU ((1 : ℂ) ⊗ₜ[ℚ] y)) =
      eW ((1 : ℂ) ⊗ₜ[ℚ] F x y))
    (u v : WeightOne.CM.Complexification U) :
    G (eU u) (eU v) = eW (LinearMap.BilinMap.baseChange ℂ F u v) := by
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
      induction v using TensorProduct.inductionOn with
      | tmul w y =>
          rw [LinearMap.BilinMap.baseChange_tmul, complexLinearMap_tmul eU z x,
            complexLinearMap_tmul eU w y]
          simp only [map_smul, LinearMap.smul_apply]
          rw [h, complexLinearMap_tmul eW (z * w) (F x y)]
          simp only [smul_smul, mul_comm]
      | add v w hv hw => simp [hv, hw]
  | add u v hu hv => simp [hu, hv]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BilinearRational.CM.Construction
