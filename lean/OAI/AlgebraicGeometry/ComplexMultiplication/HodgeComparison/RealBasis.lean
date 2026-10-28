import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HermitianMatrixPositive
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric
import Mathlib.Analysis.InnerProductSpace.NormDet

/-! # Real Basis -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RealBasis.CM.Construction

noncomputable section

section

/-! Real metric volume and complex Gram determinants agree, with their
normalizations obtained by restriction of scalars. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [InnerProductSpace ℂ F] [InnerProductSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace E] [CompleteSpace F]

omit [IsScalarTower ℝ ℂ E] [CompleteSpace E] in
theorem real_inner_complex_re (u v : E) : inner ℝ u v = (inner ℂ u v).re := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  exact (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
    (𝕜 := ℂ) u v).symm

theorem complex_adjoint_restrictScalars (T : E →L[ℂ] F) :
    (T.restrictScalars ℝ).adjoint = T.adjoint.restrictScalars ℝ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  rw [real_inner_complex_re, real_inner_complex_re]
  exact congrArg Complex.re (T.adjoint_inner_left v u)

variable [FiniteDimensional ℂ E]

local instance : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E

theorem complex_normDet_restrictScalars (T : E →L[ℂ] F) :
    (T.restrictScalars ℝ).toLinearMap.normDet = T.toLinearMap.normDet ^ 2 := by
  have h := (T.restrictScalars ℝ).normDet_sq
  rw [complex_adjoint_restrictScalars] at h
  change (T.restrictScalars ℝ).toLinearMap.normDet ^ 2 =
    (((T.adjoint.comp T).toLinearMap).restrictScalars ℝ).det at h
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply] at h
  change (T.restrictScalars ℝ).toLinearMap.normDet ^ 2 =
    Complex.normSq (T.adjoint.comp T).det at h
  rw [← T.normDet_sq] at h
  change (T.restrictScalars ℝ).toLinearMap.normDet ^ 2 =
    Complex.normSq ((T.toLinearMap.normDet ^ 2 : ℝ) : ℂ) at h
  rw [Complex.normSq_ofReal] at h
  have hn := (T.restrictScalars ℝ).toLinearMap.normDet_nonneg
  nlinarith [sq_nonneg (T.toLinearMap.normDet)]

theorem metricDensity_eq_complex_gram {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℂ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (T : E →L[ℂ] F)
    (hB : ∀ u v, B u v = inner ℝ (T u) (T v)) :
    (Metric.CM.Construction.metricDensity b.toBasis B : ℂ) = (Matrix.gram ℂ (fun i => T (c i))).det := by
  have hM : Metric.CM.Construction.metricMatrix b.toBasis B = Matrix.gram ℝ (fun i => T (b i)) := by
    ext i j
    rw [Metric.CM.Construction.metricMatrix_apply, Matrix.gram_apply]
    exact hB _ _
  have hR := (T.restrictScalars ℝ).toLinearMap.normDet_sq_eq_det_gram b
  have hC := T.toLinearMap.normDet_sq_eq_det_gram c
  change (T.restrictScalars ℝ).toLinearMap.normDet ^ 2 =
    (Matrix.gram ℝ (fun i => T (b i))).det at hR
  rw [Metric.CM.Construction.metricDensity, hM, ← hR, Real.sqrt_sq (LinearMap.normDet_nonneg _),
    complex_normDet_restrictScalars]
  exact hC

end

/-! A complex orthonormal basis and its multiples by I form a real
orthonormal basis, with the explicit paired coordinates retained. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

theorem complex_real_basis_orthonormal (b : OrthonormalBasis ι ℂ E) :
    Orthonormal ℝ (Complex.basisOneI.smulTower b.toBasis) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨a, i⟩ ⟨c, j⟩
  simp only [Module.Basis.smulTower_apply, real_inner_complex_re, inner_smul_left,
    inner_smul_right]
  fin_cases a <;> fin_cases c <;> by_cases hij : i = j <;>
    simp [Complex.basisOneI, hij]

def complexRealOrthonormalBasis (b : OrthonormalBasis ι ℂ E) :
    OrthonormalBasis (Fin 2 × ι) ℝ E :=
  (Complex.basisOneI.smulTower b.toBasis).toOrthonormalBasis (complex_real_basis_orthonormal b)

theorem complexRealOrthonormalBasis_apply (b : OrthonormalBasis ι ℂ E) (a : Fin 2) (i : ι) :
    complexRealOrthonormalBasis b (a, i) = Complex.basisOneI a • b i := by
  simp only [complexRealOrthonormalBasis, Module.Basis.coe_toOrthonormalBasis,
    Module.Basis.smulTower_apply, OrthonormalBasis.coe_toBasis]

theorem complexRealOrthonormalBasis_zero (b : OrthonormalBasis ι ℂ E) (i : ι) :
    complexRealOrthonormalBasis b (0, i) = b i := by
  rw [complexRealOrthonormalBasis_apply]
  simp [Complex.basisOneI]

theorem complexRealOrthonormalBasis_one (b : OrthonormalBasis ι ℂ E) (i : ι) :
    complexRealOrthonormalBasis b (1, i) = Complex.I • b i := by
  rw [complexRealOrthonormalBasis_apply]
  simp [Complex.basisOneI]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RealBasis.CM.Construction
