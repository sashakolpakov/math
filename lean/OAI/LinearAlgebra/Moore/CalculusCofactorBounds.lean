import OAI.Analysis.Calculus.Quaternion.IndexedCofactor

/-! Homogeneity and dimension-dependent polynomial bounds for the Moore cofactor. -/

noncomputable section
namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.Calculus.Quaternion
open scoped Matrix.Norms.Elementwise

theorem pfaffianDifferential_homogeneous (n : ℕ) (c : ℂ)
    (M N : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    pfaffianDifferential n (c • M) N = c ^ (n - 1) * pfaffianDifferential n M N := by
  classical
  have hp (σ : Equiv.Perm (Fin n × Fin 2)) (i : Fin n) :
      (∏ j ∈ Finset.univ.erase i, (c * M (σ (j, 0)) (σ (j, 1)))) =
        c ^ (n - 1) * ∏ j ∈ Finset.univ.erase i, M (σ (j, 0)) (σ (j, 1)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    simp
  unfold pfaffianDifferential
  simp only [Matrix.smul_apply, smul_eq_mul, hp]
  rw [mul_left_comm (c ^ (n - 1))]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mooreDifferential_homogeneous (n : ℕ) (c : ℝ)
    (A D : Matrix (Fin n) (Fin n) OAI.Analysis.Calculus.Quaternion.Q) :
    mooreDifferential n (c • A) D = c ^ (n - 1) * mooreDifferential n A D := by
  simp only [mooreDifferential, skewComplexify_real_smul, pfaffianDifferential_homogeneous,
    ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]

theorem rawCofactor_homogeneous (n : ℕ) (c : ℝ) (A : Matrix (Fin n) (Fin n) OAI.Analysis.Calculus.Quaternion.Q) :
    rawCofactor n (c • A) = c ^ (n - 1) • rawCofactor n A := by
  apply Matrix.ext
  intro i j
  apply Quaternion.ext <;>
    simp [rawCofactor, quaternionDualVector, mooreDifferentialLinear,
      mooreDifferential_homogeneous]

theorem mooreCofactor_homogeneous (n : ℕ) (c : ℝ) (A : Matrix (Fin n) (Fin n) OAI.Analysis.Calculus.Quaternion.Q) :
    mooreCofactor n (c • A) = c ^ (n - 1) • mooreCofactor n A := by
  rw [mooreCofactor, rawCofactor_homogeneous,
    quaternionMatrix_conjTranspose_real_smul, ← smul_add, smul_comm]
  rfl

end OAI.LinearAlgebra.Moore
namespace OAI.Analysis.Calculus.Quaternion

open OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise

theorem homogeneous_norm_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (m : ℕ) (hf : Continuous f)
    (hhom : ∀ c : ℝ, ∀ x, f (c • x) = c ^ m • f x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ m := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    by_cases hm : m = 0
    · subst m
      simpa using (hB 0 (by simp)).trans (le_max_left B 1)
    · have hz := hhom 0 (0 : E)
      simp only [zero_smul, zero_pow hm] at hz
      simp [hz, zero_pow hm]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnorm : ‖‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, hn]
  have hmem : ‖x‖⁻¹ • x ∈ Metric.closedBall (0 : E) 1 := by simp [Metric.mem_closedBall, dist_zero_right, hnorm]
  have hbound : ‖f (‖x‖⁻¹ • x)‖ ≤ max B 1 := (hB _ hmem).trans (le_max_left B 1)
  have hscale := hhom ‖x‖ (‖x‖⁻¹ • x)
  rw [smul_smul, mul_inv_cancel₀ hn, one_smul] at hscale
  rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) m)]
  exact (mul_le_mul_of_nonneg_left hbound (pow_nonneg (norm_nonneg x) m)).trans_eq (mul_comm _ _)

theorem mooreCofactor_norm_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Matrix (Fin n) (Fin n) OAI.Analysis.Calculus.Quaternion.Q,
      ‖mooreCofactor n A‖ ≤ C * ‖A‖ ^ (n - 1) := by
  exact OAI.Analysis.Calculus.Quaternion.homogeneous_norm_bound (mooreCofactor n) (n - 1)
    (contDiff_mooreCofactor n 0).continuous (mooreCofactor_homogeneous n)

theorem indexedCofactor_homogeneous {ι : Type*} [Fintype ι]
    (c : ℝ) (A : Matrix ι ι OAI.Analysis.Calculus.Quaternion.Q) :
    OAI.Analysis.Calculus.Quaternion.indexedCofactor (c • A) = c ^ (Fintype.card ι - 1) • OAI.Analysis.Calculus.Quaternion.indexedCofactor A := by
  unfold OAI.Analysis.Calculus.Quaternion.indexedCofactor
  change OAI.Analysis.Calculus.Quaternion.matrixFromFin (mooreCofactor (Fintype.card ι) (c • OAI.Analysis.Calculus.Quaternion.matrixToFin A)) = _
  rw [mooreCofactor_homogeneous]
  rfl

theorem indexedCofactor_norm_bound (ι : Type*) [Fintype ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Matrix ι ι OAI.Analysis.Calculus.Quaternion.Q,
      ‖OAI.Analysis.Calculus.Quaternion.indexedCofactor A‖ ≤ C * ‖A‖ ^ (Fintype.card ι - 1) := by
  exact OAI.Analysis.Calculus.Quaternion.homogeneous_norm_bound OAI.Analysis.Calculus.Quaternion.indexedCofactor (Fintype.card ι - 1)
    (OAI.Analysis.Calculus.Quaternion.contDiff_indexedCofactor 0).continuous OAI.Analysis.Calculus.Quaternion.indexedCofactor_homogeneous

end OAI.Analysis.Calculus.Quaternion
