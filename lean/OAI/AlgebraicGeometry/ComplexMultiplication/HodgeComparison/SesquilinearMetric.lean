import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ComplexCovector

/-! # Sesquilinear Metric -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SesquilinearMetric.CM.Construction

noncomputable section

/-! Exact inverse-Gram contraction for sesquilinear forms, proved from
the intrinsic one-covector metric in each variable. -/

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem complex_covector_pair_inverse_gram (b : Module.Basis ι ℂ E)
    (c : OrthonormalBasis κ ℂ E) (f g : E →ₗ[ℂ] ℂ) :
    (∑ l, star (f (c l)) * g (c l)) =
      ∑ j, ∑ k, star (f (b k)) * (Matrix.gram ℂ b)⁻¹ j k * g (b j) := by
  have h := ComplexCovector.CM.Construction.covectorInner_holomorphic_inverse_gram b f g
  rw [ComplexCovector.CM.Construction.covectorInner_holomorphic_basis c _ _
    (fun u => by simpa only [LinearMap.restrictScalars_apply, smul_eq_mul] using f.map_smul Complex.I u)
    (fun u => by simpa only [LinearMap.restrictScalars_apply, smul_eq_mul] using g.map_smul Complex.I u)] at h
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

theorem conjugate_covector_pair_inverse_gram (b : Module.Basis ι ℂ E)
    (c : OrthonormalBasis κ ℂ E) (f g : E →ₗ⋆[ℂ] ℂ) :
    (∑ l, star (f (c l)) * g (c l)) =
      ∑ j, ∑ k, star (f (b j)) * (Matrix.gram ℂ b)⁻¹ j k * g (b k) := by
  let F : E →ₗ[ℂ] ℂ := (starLinearEquiv ℂ).toLinearMap.comp f
  let G : E →ₗ[ℂ] ℂ := (starLinearEquiv ℂ).toLinearMap.comp g
  have h := complex_covector_pair_inverse_gram b c G F
  change (∑ l, star (star (g (c l))) * star (f (c l))) =
    ∑ j, ∑ k, star (star (g (b k))) * (Matrix.gram ℂ b)⁻¹ j k * star (f (b j)) at h
  simp only [star_star] at h
  calc
    _ = ∑ l, g (c l) * star (f (c l)) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    _ = _ := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem sesquilinear_pair_inverse_gram (b : Module.Basis ι ℂ E)
    (c : OrthonormalBasis κ ℂ E) (f g : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) :
    (∑ u, ∑ v, star (f (c u) (c v)) * g (c u) (c v)) =
      ∑ j, ∑ k, ∑ a, ∑ d, star (f (b a) (b k)) * (Matrix.gram ℂ b)⁻¹ a d *
        (Matrix.gram ℂ b)⁻¹ j k * g (b d) (b j) := by
  simp_rw [complex_covector_pair_inverse_gram b c]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = (Matrix.gram ℂ b)⁻¹ j k * ∑ u, star (f (c u) (b k)) * g (c u) (b j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = (Matrix.gram ℂ b)⁻¹ j k * ∑ a, ∑ d,
        star (f (b a) (b k)) * (Matrix.gram ℂ b)⁻¹ a d * g (b d) (b j) := by
      congr 1
      exact conjugate_covector_pair_inverse_gram b c (f.flip (b k)) (g.flip (b j))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SesquilinearMetric.CM.Construction
