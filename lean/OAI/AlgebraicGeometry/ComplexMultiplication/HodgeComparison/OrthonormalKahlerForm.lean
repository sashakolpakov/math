import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorProduct
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerFormParallel

/-! # Orthonormal Kahler Form -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OrthonormalKahlerForm.CM.Construction

noncomputable section

/-! The coframe expression agrees with the actual Kähler two-form of
the Hermitian metric, with no orientation or normalization chosen implicitly. -/

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem holomorphicRankOneForm_apply (a : E →L[ℂ] ℂ) (u v : E) :
    Powers.CM.Construction.holomorphicRankOneForm a ![u, v] =
      Complex.I * (a u * star (a v) - a v * star (a u)) := by
  unfold Powers.CM.Construction.holomorphicRankOneForm
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, Powers.CM.Construction.covectorWedge_one_one]
  rfl

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [InnerProductSpace ℝ F] [IsScalarTower ℝ ℂ F]

omit [InnerProductSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem orthonormal_basisHolomorphicCovector {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ F)
    (i : Fin n) (x : F) : CovectorProduct.CM.Construction.basisHolomorphicCovector b.toBasis i x = ⟪b i, x⟫_ℂ := by
  rw [CovectorProduct.CM.Construction.basisHolomorphicCovector_apply, OrthonormalBasis.coe_toBasis_repr]
  exact b.repr_apply_apply x i

theorem coframeKahlerForm_orthonormal_apply {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ F)
    (u v : F) : CovectorProduct.CM.Construction.coframeKahlerForm b.toBasis ![u, v] = ((⟪u, v⟫_ℂ).im : ℂ) := by
  have hs (x y : F) :
      ∑ i, CovectorProduct.CM.Construction.basisHolomorphicCovector b.toBasis i x * star (CovectorProduct.CM.Construction.basisHolomorphicCovector b.toBasis i y) =
        ⟪y, x⟫_ℂ := by
    simp_rw [orthonormal_basisHolomorphicCovector, Complex.star_def, inner_conj_symm, mul_comm]
    exact b.sum_inner_mul_inner y x
  change (1 / 2 : ℂ) * (∑ i, Powers.CM.Construction.holomorphicRankOneForm (CovectorProduct.CM.Construction.basisHolomorphicCovector b.toBasis i)) ![u, v] = _
  have he : (∑ i, Powers.CM.Construction.holomorphicRankOneForm (CovectorProduct.CM.Construction.basisHolomorphicCovector b.toBasis i)) ![u, v] =
      ∑ i, Powers.CM.Construction.holomorphicRankOneForm (CovectorProduct.CM.Construction.basisHolomorphicCovector b.toBasis i) ![u, v] := by
    exact map_sum (ContinuousAlternatingMap.applyAddHom ![u, v]) _ _
  rw [he]
  simp_rw [holomorphicRankOneForm_apply]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hs, hs, ← inner_conj_symm]
  apply Complex.ext
  all_goals
    simp only [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  all_goals norm_num
  all_goals ring

theorem real_metric_twoForm_eq_coframe {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ F)
    (f : Analysis.DifferentialForms.Manifold.Basic.FormValue F 2) (hr : ∀ v, (f v).im = 0)
    (hg : ∀ u v, KahlerDifferential.CM.Construction.metricFromTwoForm f u v = ⟪u, v⟫_ℝ) :
    f = CovectorProduct.CM.Construction.coframeKahlerForm b.toBasis := by
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv, KahlerFormParallel.CM.Construction.real_twoForm_metric_recover f _ _ (hr _), hg,
    coframeKahlerForm_orthonormal_apply, RealBasis.CM.Construction.real_inner_complex_re, inner_smul_right]
  simp

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OrthonormalKahlerForm.CM.Construction
